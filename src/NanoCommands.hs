{-# LANGUAGE CPP       #-}
{-# LANGUAGE MagicHash #-}

{-# OPTIONS -fno-cse #-}
-- -fno-cse is needed for GLOBAL_VAR's to behave properly

module NanoCommands (nanoServer) where

#include "HsVersions.h"

-- Intero
#if __GLASGOW_HASKELL__ >= 800
import           GHCi
import           GHCi.RemoteTypes
#endif
import qualified Data.Map                    as M
import           Data.Version                (showVersion)
import           GHC                         (getModuleGraph)
import           GhciFind
import           GhciInfo
import           GhciTypes
import qualified Paths_intero

-- GHCi
#if __GLASGOW_HASKELL__ >= 800
import           GHC.LanguageExtensions.Type
import           GHCi.BreakArray             as GHC
#endif
import           Debugger
import           GhciMonad                   hiding (args, runStmt)
import qualified GhciMonad                   (args, runStmt)
import           GhciTags

-- The GHC interface
import           DynFlags
import           GHC                         (BreakIndex, Ghc,
                                              InteractiveImport (..),
                                              LoadHowMuch (..), Phase, Resume,
                                              SingleStep, Target (..),
                                              TargetId (..), TyThing (..),
                                              handleSourceError)
import qualified GHC
import           GhcMonad                    (modifySession)
import           HscTypes                    (getSafeMode, handleFlagWarnings,
                                              hsc_IC, setInteractivePrintName,
                                              tyThingParent_maybe)
import           HsImpExp
import           Module
import           Name
#if __GLASGOW_HASKELL__ < 709
import           Packages                    (exposed, exposedModules,
                                              getPackageDetails, pkgIdMap,
                                              trusted)
#else
import           Packages                    (getPackageDetails,
                                              listVisibleModuleNames, trusted)
#endif
import qualified Lexer
import           PprTyThing
import           RdrName                     (getGRE_NameQualifier_maybes)
import           SrcLoc

import           StringBuffer
#if __GLASGOW_HASKELL__ < 709
import           UniqFM                      (eltsUFM)
#endif
import           Outputable                  hiding (bold, printForUser,
                                              printForUserPartWay)

-- Other random utilities
import           BasicTypes                  hiding (isTopLevel)
import           Config
import           Digraph
import           Encoding
import           FastString
import           Linker
import           Maybes                      (expectJust, orElse)
import           NameSet
import           Panic                       hiding (showException)
import           Util

-- Haskell Libraries

import           Control.Applicative         hiding (empty)
import           Control.Monad               as Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Class

import           Data.Array
import qualified Data.ByteString.Char8       as BS
import           Data.Char
import           Data.Function
import           Data.IORef                  (IORef, readIORef, writeIORef)
import           Data.List                   (find, group, intercalate,
                                              intersperse, isPrefixOf, nub,
                                              partition, sort, sortBy)
import           Data.Maybe

import           Exception                   hiding (catch)

import           Foreign.C
#if __GLASGOW_HASKELL__ < 709
import           Foreign.Safe
#else
import           Foreign
#endif

import           System.Directory
import           System.Environment
import           System.Exit                 (ExitCode (..), exitSuccess,
                                              exitWith)
import           System.FilePath
import           System.IO
import           System.IO.Error
import           System.IO.Unsafe            (unsafePerformIO)
import           System.Process
import           Text.Printf
import           Text.Read                   (readMaybe)

#ifndef mingw32_HOST_OS
import           System.Posix                hiding (getEnv)
#else
import qualified System.Win32
#endif

import           GHC.Exts                    (unsafeCoerce#)
import           GHC.IO.Exception            (IOErrorType (InvalidArgument))
import           GHC.IO.Handle               (hFlushAll)
import           GHC.TopHandler              (topHandler)

-- import           Control.Concurrent (forkIO, MVar, newEmptyMVar, putMVar, takeMVar)
import qualified GHC.SYB.Utils               as SYBU
import           Nanomsg

import           Common

type NanoCommand = (String, String -> GHCi String)

nanoCommands :: [NanoCommand]
nanoCommands = [
  ("check",     checkModule')
  ]

exit' :: Socket Rep -> Endpoint -> String -> GHCi ()
exit' socket endpoint _ = liftIO $ do
            shutdown socket endpoint
            exitSuccess

nanoServer :: GHCi ()
nanoServer = do
            -- bind nanomsg socket and save into GHCiState
            socket <- liftIO $ socket Rep
            endpoint <- liftIO $ bind socket "ipc:///tmp/intero.socket"

            let quit = exit' socket endpoint

            -- enter the req/rep loop
            _ <- liftIO $ putStrLn "entering req/rep loop..."
            forever $ do
              msg <- liftIO $ recv socket
              let cmd = BS.unpack msg
              liftIO $ putStrLn $ "received: " ++ cmd

              when (cmd == "quit") $ quit ""

              -- TODO dispatch commands
              -- TODO check result + behaviour of handler'
              result <- runOneCommand' handler' checkModule' cmd

              liftIO $ send socket $ BS.pack result


runOneCommand' :: (SomeException -> GHCi String) -> (String -> GHCi String) -> String -> GHCi String
runOneCommand' eh gCmd s =
    ghciHandle (\e -> eh e >>= return) $
             handleSourceError printErrorAndKeepGoing (gCmd s)
  where
    printErrorAndKeepGoing err = do
        GHC.printException err
        return "Continue.. TODO"

handler' :: SomeException -> GHCi String
handler' exception = do
  flushInterpBuffers
  liftIO installSignalHandlers
  ghciHandle handler' (showException exception >> return "Exception")

-----------------------------------------------------------------------------
-- :check

checkModule' :: String -> GHCi String
checkModule' m = do
  let modl = GHC.mkModuleName m
  result <- handleSourceError (\e -> GHC.printException e >> return "Error") $ do
          r <- GHC.typecheckModule =<< GHC.parseModule =<< GHC.getModSummary modl
          dflags <- getDynFlags

          let result = SYBU.showData SYBU.Parser 2 (GHC.pm_parsed_source (GHC.tm_parsed_module r))
              names = showSDoc dflags (case GHC.moduleInfo r of
                        cm | Just scope <- GHC.modInfoTopLevelScope cm ->
                            let
                                (loc, glob) = ASSERT( all isExternalName scope )
                                              partition ((== modl) . GHC.moduleName . GHC.nameModule) scope
                            in
                                    (text "global names: " <+> ppr glob) $$
                                    (text "local  names: " <+> ppr loc)
                        _ -> empty)

          return $ "@checkModule: " ++ result ++ "\n" ++ names
  case result of
    "Error" -> afterLoad' (Failed, result) False
    _ -> afterLoad' (Succeeded, result) False

afterLoad' :: (SuccessFlag, String)
          -> Bool         -- keep the remembered_ctx, as far as possible (:reload)
          -> GHCi String
afterLoad' (ok, result) retain_context = do
  revertCAFs  -- always revert CAFs on load.
  discardTickArrays
  loaded_mod_summaries <- getLoadedModules
  let loaded_mods = map GHC.ms_mod loaded_mod_summaries
  modulesLoadedMsg' ok loaded_mods
  setContextAfterLoad retain_context loaded_mod_summaries
  return result

modulesLoadedMsg' :: SuccessFlag -> [Module] -> GHCi ()
modulesLoadedMsg' ok mods = do
  dflags <- getDynFlags
  unqual <- GHC.getPrintUnqual
  let mod_commas
        | null mods = text "none."
        | otherwise = hsep (
            punctuate comma (map ppr mods)) <> text "."
      status = case ok of
                   Failed    -> text "Failed"
                   Succeeded -> text "Ok"

      msg = status <> text ", modules loaded:" <+> mod_commas

  when (verbosity dflags > 0) $
     liftIO $ putStrLn $ showSDocForUser dflags unqual msg
