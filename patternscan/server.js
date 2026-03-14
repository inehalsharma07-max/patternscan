/**
 * PatternScan – Node.js Backend
 * Run: node server.js
 * Open: http://localhost:3001
 *
 * All Yahoo Finance fetches happen here (server-side) → zero CORS issues.
 */

const http  = require('http');
const https = require('https');
const fs    = require('fs');
const path  = require('path');
const url   = require('url');

const PORT = 3001;

// ─── MIME types ───────────────────────────────────────────────────────────────
const MIME = {
  '.html': 'text/html',
  '.js':   'application/javascript',
  '.css':  'text/css',
  '.json': 'application/json',
};

// ─── Fetch helper (server-side HTTPS) ─────────────────────────────────────────
function fetchJSON(targetUrl) {
  return new Promise((resolve, reject) => {
    const options = {
      headers: {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120 Safari/537.36',
        'Accept': 'application/json,*/*',
        'Accept-Language': 'en-US,en;q=0.9',
        'Accept-Encoding': 'identity',
        'Cache-Control': 'no-cache',
      },
      timeout: 12000,
    };

    const req = https.get(targetUrl, options, (res) => {
      if (res.statusCode === 302 || res.statusCode === 301) {
        return fetchJSON(res.headers.location).then(resolve).catch(reject);
      }
      if (res.statusCode !== 200) {
        return reject(new Error(`HTTP ${res.statusCode}`));
      }
      let data = '';
      res.on('data', chunk => data += chunk);
      res.on('end', () => {
        try { resolve(JSON.parse(data)); }
        catch (e) { reject(new Error('JSON parse failed')); }
      });
    });
    req.on('error', reject);
    req.on('timeout', () => { req.destroy(); reject(new Error('Timeout')); });
  });
}

// ─── Yahoo Finance price fetch ─────────────────────────────────────────────────
// Timeframe config: interval → best default range for Yahoo Finance
const TF_CONFIG = {
  '15m':  { interval: '15m',  range: '60d',  label: '15 min' },
  '30m':  { interval: '30m',  range: '60d',  label: '30 min' },
  '1h':   { interval: '60m',  range: '6mo',  label: '1 Hour'  },
  '4h':   { interval: '60m',  range: '6mo',  label: '4 Hour'  }, // aggregated client-side
  '1d':   { interval: '1d',   range: '1y',   label: 'Daily'   },
  '1wk':  { interval: '1wk',  range: '3y',   label: 'Weekly'  },
};

// Aggregate candles (e.g. 4 x 1h → 1 x 4h)
function aggregateCandles(prices, dates, n) {
  if (n <= 1) return { prices, dates };
  const outP = [], outD = [];
  for (let i = 0; i + n <= prices.length; i += n) {
    const slice = prices.slice(i, i + n);
    outP.push(slice[slice.length - 1]); // close of last candle in group
    outD.push(dates[i + n - 1] || dates[i]);
  }
  return { prices: outP, dates: outD };
}

async function getStockData(symbol, timeframe) {
  const tf  = TF_CONFIG[timeframe] || TF_CONFIG['1d'];
  const endpoint = `https://query1.finance.yahoo.com/v8/finance/chart/${encodeURIComponent(symbol)}?interval=${tf.interval}&range=${tf.range}`;

  const json = await fetchJSON(endpoint);
  const result = json?.chart?.result?.[0];
  if (!result) throw new Error('No chart data returned');

  const closes    = result.indicators.quote[0].close;
  const timestamps = result.timestamp || [];

  const pairs = timestamps
    .map((t, i) => [t * 1000, closes[i]])
    .filter(([, c]) => c != null && !isNaN(c));

  if (pairs.length < 8) throw new Error('Insufficient price history');

  let prices = pairs.map(([, c]) => c);
  let dates  = pairs.map(([t]) => {
    const d = new Date(t);
    if (tf.interval === '1d' || tf.interval === '1wk') return d.toISOString().slice(0, 10);
    return d.toISOString().slice(0, 16).replace('T', ' ');
  });

  // Aggregate 1h → 4h if requested
  if (timeframe === '4h') {
    const agg = aggregateCandles(prices, dates, 4);
    prices = agg.prices; dates = agg.dates;
  }

  if (prices.length < 8) throw new Error('Insufficient data after aggregation');

  const last = prices[prices.length - 1];
  const prev = prices[prices.length - 2];

  return {
    symbol, prices, dates,
    price:     parseFloat(last.toFixed(2)),
    change:    parseFloat(((last - prev) / prev * 100).toFixed(2)),
    timeframe: tf.label,
  };
}

// ─── Pattern matching (Pearson correlation with sliding window) ────────────────
function normalize(arr) {
  const mn = Math.min(...arr), mx = Math.max(...arr);
  if (mx === mn) return arr.map(() => 0.5);
  return arr.map(v => (v - mn) / (mx - mn));
}

function resample(arr, len) {
  if (arr.length === len) return arr;
  const out = [];
  for (let i = 0; i < len; i++) {
    const pos = (i / (len - 1)) * (arr.length - 1);
    const lo  = Math.floor(pos);
    const hi  = Math.min(lo + 1, arr.length - 1);
    out.push(arr[lo] * (1 - (pos - lo)) + arr[hi] * (pos - lo));
  }
  return out;
}

function pearson(a, b) {
  const n  = a.length;
  const ma = a.reduce((s, v) => s + v, 0) / n;
  const mb = b.reduce((s, v) => s + v, 0) / n;
  let num = 0, da = 0, db = 0;
  for (let i = 0; i < n; i++) {
    const A = a[i] - ma, B = b[i] - mb;
    num += A * B; da += A * A; db += B * B;
  }
  if (da === 0 || db === 0) return 0;
  return num / Math.sqrt(da * db);
}

function findBestMatch(prices, template, recentFraction = 0.4) {
  const tmpl = normalize(template.map(y => 1 - y));
  const N    = prices.length;

  // Any window that ENDS in the last recentFraction of candles is flagged "recent".
  // e.g. recentFraction=0.4, N=252 → candle 151+ is "recent zone".
  const recentCutoff = Math.floor(N * (1 - recentFraction));

  // Scan ALL history with varied window sizes (15%–70%).
  // Large enough to have shape, varied enough to catch different pattern lengths.
  const ratios   = [0.15, 0.20, 0.28, 0.36, 0.45, 0.55, 0.65, 0.70];
  const minWin   = Math.max(template.length + 2, 8);
  const winSizes = [...new Set(
    ratios.map(r => Math.round(N * r)).filter(w => w >= minWin && w <= N)
  )];

  let best = { score: -1, start: 0, end: N - 1, matchPrices: prices.slice(-1) };

  for (const wSz of winSizes) {
    for (let st = 0; st <= N - wSz; st++) {
      const win  = prices.slice(st, st + wSz);
      const winN = resample(normalize(win), tmpl.length);
      const corr = pearson(tmpl, winN);
      const end  = st + wSz - 1;
      if (corr > best.score) {
        best = { score: corr, start: st, end, matchPrices: win };
      }
    }
  }

  // Flag whether the best match ended in the recent zone
  const isRecent = best.end >= recentCutoff;
  return { ...best, isRecent };
}

// ─── API handlers ──────────────────────────────────────────────────────────────

// GET /api/stock?symbol=RELIANCE.NS&range=3mo
async function handleStockAPI(query, res) {
  const { symbol, timeframe } = query;
  if (!symbol) return sendJSON(res, 400, { error: 'symbol required' });

  try {
    const data = await getStockData(symbol, timeframe || '1d');
    sendJSON(res, 200, data);
  } catch (e) {
    sendJSON(res, 500, { error: e.message });
  }
}

// POST /api/scan  { symbols:[...], range, template:[...], threshold }
async function handleScanAPI(body, res) {
  let parsed;
  try { parsed = JSON.parse(body); } catch { return sendJSON(res, 400, { error: 'Invalid JSON' }); }

  const { symbols, timeframe, template, threshold, recency } = parsed;
  if (!Array.isArray(symbols) || !Array.isArray(template)) {
    return sendJSON(res, 400, { error: 'symbols and template arrays required' });
  }

  const minScore       = parseFloat(threshold) || 0.70;
  const recentFraction = parseFloat(recency)    || 0.35;
  const results  = [];
  const errors   = [];

  for (const sym of symbols) {
    try {
      const data  = await getStockData(sym.symbol, timeframe || '1d');
      const match = findBestMatch(data.prices, template, recentFraction);

      if (match.score >= minScore) {
        const daysAgo = data.prices.length - 1 - match.end;
        results.push({
          symbol:      sym.symbol,
          name:        sym.name,
          score:       parseFloat(match.score.toFixed(4)),
          price:       data.price,
          change:      data.change,
          prices:      data.prices,
          dates:       data.dates,
          matchStart:  match.start,
          matchEnd:    match.end,
          matchPrices: match.matchPrices,
          daysAgo,
          isRecent:    match.isRecent === true,
          timeframe:   data.timeframe,
        });
      }
    } catch (e) {
      errors.push({ symbol: sym.symbol, error: e.message });
    }
    // Small delay to be polite to Yahoo Finance
    await sleep(80);
  }

  // Sort by score desc
  results.sort((a, b) => b.score - a.score);
  sendJSON(res, 200, { results, errors, total: symbols.length, matched: results.length });
}

// ─── Utilities ─────────────────────────────────────────────────────────────────
function sendJSON(res, status, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(status, {
    'Content-Type': 'application/json',
    'Access-Control-Allow-Origin': '*',
    'Content-Length': Buffer.byteLength(body),
  });
  res.end(body);
}

function sleep(ms) { return new Promise(r => setTimeout(r, ms)); }

function serveFile(filePath, res) {
  fs.readFile(filePath, (err, data) => {
    if (err) {
      res.writeHead(404); res.end('Not found');
      return;
    }
    const ext  = path.extname(filePath);
    const mime = MIME[ext] || 'text/plain';
    res.writeHead(200, { 'Content-Type': mime });
    res.end(data);
  });
}

// ─── Main HTTP Server ──────────────────────────────────────────────────────────
const server = http.createServer((req, res) => {
  const parsed   = url.parse(req.url, true);
  const pathname = parsed.pathname;

  console.log(`  ${req.method} ${pathname}`);

  // CORS — set on every response
  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader('Access-Control-Allow-Methods', 'GET,POST,OPTIONS');
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type');

  if (req.method === 'OPTIONS') {
    res.writeHead(204); return res.end();
  }

  // Health check — instant, no Yahoo call
  if (pathname === '/api/health') {
    return sendJSON(res, 200, { ok: true, ts: Date.now() });
  }

  // Single stock fetch
  if (pathname === '/api/stock' && req.method === 'GET') {
    return handleStockAPI(parsed.query, res);
  }

  // Batch scan
  if (pathname === '/api/scan' && req.method === 'POST') {
    let body = '';
    req.on('data', c => { body += c; });
    req.on('end', () => handleScanAPI(body, res));
    return;
  }

  // Static files
  if (pathname === '/' || pathname === '/index.html') {
    return serveFile(path.join(__dirname, 'public', 'index.html'), res);
  }

  const safePath = path.join(__dirname, 'public', path.normalize(pathname));
  if (safePath.startsWith(path.join(__dirname, 'public'))) {
    return serveFile(safePath, res);
  }

  console.log(`  404: ${pathname}`);
  res.writeHead(404, { 'Content-Type': 'text/plain' });
  res.end('Not found: ' + pathname);
});

server.listen(PORT, () => {
  console.log(`\n  ◉ PatternScan server running`);
  console.log(`  → Open http://localhost:${PORT}\n`);
});

server.on('error', (e) => {
  if (e.code === 'EADDRINUSE') {
    console.error(`\n  ✗ Port ${PORT} is already in use. Kill the other process or change PORT.\n`);
  } else {
    console.error('Server error:', e);
  }
  process.exit(1);
});
