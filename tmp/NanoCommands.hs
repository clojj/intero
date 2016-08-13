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
import           System.Exit                 (ExitCode (..), exitWith)
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
import           System.Exit


nanoServer :: GHCi ()
nanoServer = do
            -- bind nanomsg socket and save into GHCiState
            socket <- liftIO $ socket Rep
            endpoint <- liftIO $ bind socket "ipc:///tmp/intero.socket"

            -- enter the req/rep loop
            _ <- liftIO $ putStrLn "entering req/rep loop..."
            forever $ do
              msg <- liftIO $ recv socket
              let cmd = BS.unpack msg
              liftIO $ putStrLn $ "received: " ++ cmd

              when (cmd == ":quit") $ liftIO $ do
                shutdown socket endpoint
                exitSuccess

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

showException :: SomeException -> GHCi ()
showException se =
  liftIO $ case fromException se of
           -- omit the location for CmdLineError:
           Just (CmdLineError s)    -> putException s
           -- ditto:
           -- Just ph@(PhaseFailed {}) -> putException (showGhcException ph "")
           Just other_ghc_ex        -> putException (show other_ghc_ex)
           Nothing                  ->
               case fromException se of
               Just UserInterrupt -> putException "Interrupted."
               _                  -> putException ("*** Exception: " ++ show se)
  where
    putException = hPutStrLn stderr

ghciHandle :: (HasDynFlags m, ExceptionMonad m) => (SomeException -> m a) -> m a -> m a
ghciHandle h m = gmask $ \restore -> do
                 dflags <- getDynFlags
                 gcatch (restore (GHC.prettyPrintGhcErrors dflags m)) $ \e -> restore (h e)

ghciTry :: GHCi a -> GHCi (Either SomeException a)
ghciTry (GHCi m) = GHCi $ \s -> gtry (m s)

tryBool :: GHCi a -> GHCi Bool
tryBool m = do
    r <- ghciTry m
    case r of
      Left _  -> return False
      Right _ -> return True

checkAdd ii = do
  dflags <- getDynFlags
  let safe = safeLanguageOn dflags
  case ii of
    IIModule modname
       | safe -> throwGhcException $ CmdLineError "can't use * imports with Safe Haskell"
       | otherwise -> wantInterpretedModuleName modname >> return ()

    IIDecl d -> do
       let modname = unLoc (ideclName d)
           pkgqual = ideclPkgQual d
       m <- GHC.lookupModule modname (fmap sl_fs pkgqual)
       when safe $ do
           t <- GHC.isModuleTrusted m
           when (not t) $ throwGhcException $ ProgramError $ ""

wantInterpretedModuleName :: GHC.GhcMonad m => ModuleName -> m Module
wantInterpretedModuleName modname = do
   modl <- lookupModuleName modname
   let str = moduleNameString modname
   dflags <- getDynFlags
   when (modulePackage modl /= thisPackage dflags) $
      throwGhcException (CmdLineError ("module '" ++ str ++ "' is from another package;\nthis command requires an interpreted module"))
   is_interpreted <- GHC.moduleIsInterpreted modl
   when (not is_interpreted) $
       throwGhcException (CmdLineError ("module '" ++ str ++ "' is not interpreted; try \':add *" ++ str ++ "' first"))
   return modl


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

discardTickArrays :: GHCi ()
discardTickArrays = do
   st <- getGHCiState
   setGHCiState st{tickarrays = emptyModuleEnv}

getLoadedModules :: GHC.GhcMonad m => m [GHC.ModSummary]
getLoadedModules = do
  graph <- GHC.getModuleGraph
  filterM (GHC.isLoaded . GHC.ms_mod_name) graph


modulesLoadedMsg' :: SuccessFlag -> [Module] -> GHCi String
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

  if verbosity dflags > 0 then
     return $ showSDocForUser dflags unqual msg
  else
     return ""

setContextAfterLoad :: Bool -> [GHC.ModSummary] -> GHCi ()
setContextAfterLoad keep_ctxt [] = do
  setContextKeepingPackageModules keep_ctxt []
setContextAfterLoad keep_ctxt ms = do
  -- load a target if one is available, otherwise load the topmost module.
  targets <- GHC.getTargets
  case [ m | Just m <- map (findTarget ms) targets ] of
        []    ->
          let graph' = flattenSCCs (GHC.topSortModuleGraph True ms Nothing) in
          load_this (last graph')
        (m:_) ->
          load_this m
 where
   findTarget mds t
    = case filter (`matches` t) mds of
        []    -> Nothing
        (m:_) -> Just m

   summary `matches` Target (TargetModule m) _ _
        = GHC.ms_mod_name summary == m
   summary `matches` Target (TargetFile f _) _ _
        | Just f' <- GHC.ml_hs_file (GHC.ms_location summary)   = f == f'
   _ `matches` _
        = False

   load_this summary | m <- GHC.ms_mod summary = do
        is_interp <- GHC.moduleIsInterpreted m
        dflags <- getDynFlags
        let star_ok = is_interp && not (safeLanguageOn dflags)
              -- We import the module with a * iff
              --   - it is interpreted, and
              --   - -XSafe is off (it doesn't allow *-imports)
        let new_ctx | star_ok   = [mkIIModule (GHC.moduleName m)]
                    | otherwise = [mkIIDecl   (GHC.moduleName m)]
        setContextKeepingPackageModules keep_ctxt new_ctx

setContextKeepingPackageModules
        :: Bool                 -- True  <=> keep all of remembered_ctx
                                -- False <=> just keep package imports
        -> [InteractiveImport]  -- new context
        -> GHCi ()

setContextKeepingPackageModules keep_ctx trans_ctx = do

  st <- getGHCiState
  let rem_ctx = remembered_ctx st
  new_rem_ctx <- if keep_ctx then return rem_ctx
                             else keepPackageImports rem_ctx
  setGHCiState st{ remembered_ctx = new_rem_ctx,
                   transient_ctx  = filterSubsumed new_rem_ctx trans_ctx }
  setGHCContextFromGHCiState

keepPackageImports :: [InteractiveImport] -> GHCi [InteractiveImport]
keepPackageImports = filterM is_pkg_import
  where
     is_pkg_import :: InteractiveImport -> GHCi Bool
     is_pkg_import (IIModule _) = return False
     is_pkg_import (IIDecl d)
         = do e <- gtry $ GHC.findModule mod_name (fmap sl_fs $ ideclPkgQual d)
              case e :: Either SomeException Module of
                Left _  -> return False
                Right m -> return (not (isHomeModule m))
        where
          mod_name = unLoc (ideclName d)

-- | @filterSubsumed is js@ returns the elements of @js@ not subsumed
-- by any of @is@.
filterSubsumed :: [InteractiveImport] -> [InteractiveImport]
               -> [InteractiveImport]
filterSubsumed is js = filter (\j -> not (any (`iiSubsumes` j) is)) js

setGHCContextFromGHCiState :: GHCi ()
setGHCContextFromGHCiState = do
  st <- getGHCiState
      -- re-use checkAdd to check whether the module is valid.  If the
      -- module does not exist, we do *not* want to print an error
      -- here, we just want to silently keep the module in the context
      -- until such time as the module reappears again.  So we ignore
      -- the actual exception thrown by checkAdd, using tryBool to
      -- turn it into a Bool.
  iidecls <- filterM (tryBool.checkAdd) (transient_ctx st ++ remembered_ctx st)
  dflags <- GHC.getSessionDynFlags
  GHC.setContext $
     if xopt compat_ImplicitPrelude dflags && not (any isPreludeImport iidecls)
        then iidecls ++ [implicitPreludeImport]
        else iidecls
    -- XXX put prel at the end, so that guessCurrentModule doesn't pick it up.


-- -----------------------------------------------------------------------------
-- Utils on InteractiveImport

mkIIModule :: ModuleName -> InteractiveImport
mkIIModule = IIModule

mkIIDecl :: ModuleName -> InteractiveImport
mkIIDecl = IIDecl . simpleImportDecl

lookupModuleName :: GHC.GhcMonad m => ModuleName -> m Module
lookupModuleName mName = GHC.lookupModule mName Nothing

isHomeModule :: Module -> Bool
#if  __GLASGOW_HASKELL__ >= 800
isHomeModule m = modulePackage m == mainUnitId
#elif __GLASGOW_HASKELL__ < 709
isHomeModule m = modulePackage m == mainPackageId
#else
isHomeModule m = modulePackage m == mainPackageKey
#endif

iiSubsumes :: InteractiveImport -> InteractiveImport -> Bool
iiSubsumes (IIModule m1) (IIModule m2) = m1==m2
iiSubsumes (IIDecl d1) (IIDecl d2)      -- A bit crude
  =  unLoc (ideclName d1) == unLoc (ideclName d2)
     && ideclAs d1 == ideclAs d2
     && (not (ideclQualified d1) || ideclQualified d2)
     && (idhd1 `hidingSubsumes` idhd2)
  where
-- I'm not so sure about this fix here...
#if __GLASGOW_HASKELL__ < 709
     idhd2 = ideclHiding d2
     idhd1 = ideclHiding d1
#else
     idhd2 = fmap (fmap unLoc) $ ideclHiding d2
     idhd1 = fmap (fmap unLoc) $ ideclHiding d1
#endif
     _                `hidingSubsumes` Just (False,[]) = True
     Just (False, xs) `hidingSubsumes` Just (False,ys) = all (`elem` xs) ys
     h1               `hidingSubsumes` h2              = h1 == h2
iiSubsumes _ _ = False

#if __GLASGOW_HASKELL__ >= 800
packageString :: UnitId -> String
packageString = unitIdString
modulePackage :: Module -> UnitId
modulePackage = moduleUnitId
#elif __GLASGOW_HASKELL__ < 709
packageString :: PackageId -> String
packageString = packageIdString
modulePackage :: Module -> PackageId
modulePackage = modulePackageId
#else
packageString :: PackageKey -> String
packageString = packageKeyString
modulePackage :: Module -> PackageKey
modulePackage = modulePackageKey
#endif

#if __GLASGOW_HASKELL__ >= 800
compat_ImplicitPrelude :: Extension
compat_ImplicitPrelude =
  ImplicitPrelude
#else
compat_ImplicitPrelude :: ExtensionFlag
compat_ImplicitPrelude =
  Opt_ImplicitPrelude
#endif

preludeModuleName :: ModuleName
preludeModuleName = GHC.mkModuleName "Prelude"

implicitPreludeImport :: InteractiveImport
implicitPreludeImport = IIDecl (simpleImportDecl preludeModuleName)

isPreludeImport :: InteractiveImport -> Bool
isPreludeImport (IIModule {}) = True
isPreludeImport (IIDecl d)    = unLoc (ideclName d) == preludeModuleName
