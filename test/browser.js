// drive headless Chrome over CDP: load the app, wait for the analysis, collect console errors, screenshot each tab
const { spawn } = require('child_process'); const fs = require('fs');
const url = process.argv[2], out = process.argv[3] || '/tmp/shot';
const chrome = spawn('google-chrome', ['--headless=new', '--no-sandbox', '--disable-gpu', '--remote-debugging-port=9333', '--window-size=1440,1800', 'about:blank'], { stdio: 'ignore' });
const sleep = ms => new Promise(r => setTimeout(r, ms));
(async () => {
  let ws;
  for (let i = 0; i < 50; i++) { try { const l = await (await fetch('http://127.0.0.1:9333/json')).json(); const p = l.find(x => x.type === 'page'); if (p) { ws = new WebSocket(p.webSocketDebuggerUrl); break; } } catch (e) { } await sleep(200); }
  await new Promise(r => ws.onopen = r);
  let id = 0; const pend = new Map(); const logs = [];
  ws.onmessage = m => { const d = JSON.parse(m.data); if (d.id && pend.has(d.id)) { pend.get(d.id)(d); pend.delete(d.id); } else if (d.method === 'Runtime.consoleAPICalled') logs.push(d.params.type + ': ' + d.params.args.map(a => a.value || a.description).join(' ')); else if (d.method === 'Runtime.exceptionThrown') logs.push('EXC: ' + JSON.stringify(d.params.exceptionDetails.exception && d.params.exceptionDetails.exception.description || d.params.exceptionDetails.text)); };
  const send = (method, params) => new Promise(r => { const i = ++id; pend.set(i, r); ws.send(JSON.stringify({ id: i, method, params: params || {} })); });
  const ev = async e => (await send('Runtime.evaluate', { expression: e, awaitPromise: true, returnByValue: true })).result.result.value;
  await send('Runtime.enable'); await send('Page.enable');
  await send('Emulation.setDeviceMetricsOverride', { width: 1440, height: 1800, deviceScaleFactor: 1, mobile: false });
  if (process.env.DARK) await send('Emulation.setEmulatedMedia', { features: [{ name: 'prefers-color-scheme', value: 'dark' }] });
  await send('Page.navigate', { url });
  for (let i = 0; i < (process.env.NOWAIT ? 4 : 300); i++) { await sleep(500); const s = await ev("document.getElementById('status') && document.getElementById('status').textContent"); if (s && /^Done|failed|error/i.test(s)) { console.log('status:', s); break; } }
  if (process.env.EXAMPLE) { await ev(`(function(){var s=document.getElementById('example');s.value='${process.env.EXAMPLE}';s.onchange();})()`); await sleep(1000); for (let i = 0; i < 300; i++) { await sleep(500); const s = await ev("document.getElementById('status').textContent"); if (/^Done/.test(s)) { console.log('status:', s); break; } } }
  const tabs = (process.env.TABS || 'stats').split(',');
  for (const t of tabs) {
    await ev(`(document.querySelector('[data-tab=${t}]')||{click(){}}).click()`); await sleep(300);
    const shot = await send('Page.captureScreenshot', { format: 'png', captureBeyondViewport: false });
    fs.writeFileSync(out + '_' + t + '.png', Buffer.from(shot.result.data, 'base64'));
  }
  if (process.env.EVAL) console.log(await ev(process.env.EVAL));
  console.log(logs.join('\n') || 'no console output');
  ws.close(); chrome.kill(); process.exit(0);
})().catch(e => { console.error(e); chrome.kill(); process.exit(1); });
