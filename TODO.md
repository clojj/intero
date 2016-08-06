dual input from
- MVar nanomsg
- stdin

==============================
Test:
var Nano = require('nanomsg');
var req = Nano.socket('req');
var addr = 'ipc:///tmp/intero.socket';
req.connect(addr);
req.on('data', function (data) { console.log('received response: ' + data) });

req.send(':check Lib\n');
==============================

 