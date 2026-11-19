// Build: bundle the library (src/*.js + C runtime) into dist/pl2detlog.js and the app into one self-contained dist/index.html
const fs = require('fs'); const path = require('path');
const R = p => fs.readFileSync(path.join(__dirname, p), 'utf8');
const order = ['core', 'engine', 'builtins', 'swi', 'convert', 'detlog_engine', 'native', 'detlog_fast', 'detlog_interp', 'backconv', 'algebra', 'rewrite', 'cgen', 'proof', 'stats', 'cref', 'examples', 'thermo', 'interp'];
const crt = "(function(P){P.C_RUNTIME=" + JSON.stringify(R('src/runtime.c')) + ";P.DETLOG_RUNTIME_PL=" + JSON.stringify(R('src/detlog_runtime.pl')) + ";})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));\n";
const lib = '/* pl2detlog library — Prolog to Detlog. BSD-3-Clause. github.com/luciangreen/pl2detlog */\n' + order.map(f => R('src/' + f + '.js')).join('\n') + crt;
if (/<\/script/i.test(lib)) throw new Error('library contains </script');
fs.mkdirSync(path.join(__dirname, 'dist'), { recursive: true });
fs.writeFileSync(path.join(__dirname, 'dist/pl2detlog.js'), lib);
const html = R('app/index.src.html').replace('/*__LIB__*/', () => lib).replace('/*__RTPL__*/', () => R('src/detlog_runtime.pl')).replace('/*__APP__*/', () => R('app/app.js'));
fs.writeFileSync(path.join(__dirname, 'dist/index.html'), html);
fs.writeFileSync(path.join(__dirname, 'index.html'), html);
console.log('built dist/index.html', (html.length / 1024).toFixed(0) + ' KB');
