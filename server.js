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
  '1m':   { interval: '1m',   range: '7d',   label: '1 Min'   },
  '5m':   { interval: '5m',   range: '60d',  label: '5 Min'   },
  '15m':  { interval: '15m',  range: '60d',  label: '15 Min'  },
  '30m':  { interval: '30m',  range: '60d',  label: '30 Min'  },
  '1h':   { interval: '60m',  range: '6mo',  label: '1 Hour'  },
  '4h':   { interval: '60m',  range: '6mo',  label: '4 Hour'  },
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

// ═══════════════════════════════════════════════════════
// PATTERN CONFIRMATION ENGINE
// Each pattern has a specific technical condition that must
// be TRUE at the END of the match window (last 1-3 candles).
// This ensures only freshly triggered patterns are shown.
// ═══════════════════════════════════════════════════════

function swingHighs(arr, minGap=2) {
  const h=[];
  for(let i=1;i<arr.length-1;i++){
    if(arr[i]>arr[i-1]&&arr[i]>arr[i+1]){
      if(!h.length||i-h[h.length-1].i>=minGap) h.push({i,v:arr[i]});
    }
  }
  return h;
}
function swingLows(arr, minGap=2) {
  const l=[];
  for(let i=1;i<arr.length-1;i++){
    if(arr[i]<arr[i-1]&&arr[i]<arr[i+1]){
      if(!l.length||i-l[l.length-1].i>=minGap) l.push({i,v:arr[i]});
    }
  }
  return l;
}

function confirmPattern(win, patternType) {
  if (!patternType) return { confirmed: true, reason: null };
  const N    = win.length;
  const last = win[N-1];
  // Use last 3 candles to check freshness of the break
  const recentMin = Math.min(...win.slice(-3));
  const recentMax = Math.max(...win.slice(-3));
  // Body = everything except the last 15% of candles (the "trigger zone")
  const bodyEnd  = Math.floor(N * 0.85);
  const bodyPrices = win.slice(0, bodyEnd);

  switch(patternType) {

    case 'lower_hl': {
      // Condition: price just broke BELOW the previous lowest swing low
      const lows = swingLows(win.slice(0, bodyEnd));
      if (!lows.length) return { confirmed: false };
      const prevLow = Math.min(...lows.map(l => l.v));
      const broke   = recentMin < prevLow * 0.9985;
      return { confirmed: broke, reason: broke ? 'Lower low broken' : null };
    }

    case 'higher_hl': {
      // Condition: price just broke ABOVE the previous highest swing high
      const highs = swingHighs(win.slice(0, bodyEnd));
      if (!highs.length) return { confirmed: false };
      const prevHigh = Math.max(...highs.map(h => h.v));
      const broke    = recentMax > prevHigh * 1.0015;
      return { confirmed: broke, reason: broke ? 'Higher high broken' : null };
    }

    case 'head_shoulders': {
      // Neckline = avg of the two troughs between/around the three peaks
      const lows = swingLows(win);
      if (lows.length < 2) return { confirmed: false };
      // Pick the two lowest troughs (left of head and right of head)
      const sorted  = [...lows].sort((a,b)=>a.v-b.v);
      const neckAvg = (sorted[0].v + (sorted[1]?.v || sorted[0].v)) / 2;
      const broke   = recentMin < neckAvg * 0.9985;
      return { confirmed: broke, reason: broke ? 'Neckline broken down' : null };
    }

    case 'inv_head_shoulders': {
      // Neckline = avg of the two peaks on either side of the inverted head
      const highs = swingHighs(win);
      if (highs.length < 2) return { confirmed: false };
      const sorted  = [...highs].sort((a,b)=>b.v-a.v);
      const neckAvg = (sorted[0].v + (sorted[1]?.v || sorted[0].v)) / 2;
      const broke   = recentMax > neckAvg * 1.0015;
      return { confirmed: broke, reason: broke ? 'Neckline broken up' : null };
    }

    case 'double_top': {
      // Support = lowest point between the two tops (mid-section trough)
      const mid        = Math.floor(N * 0.5);
      const midSection = win.slice(Math.floor(N*0.2), Math.floor(N*0.8));
      const support    = Math.min(...midSection);
      const broke      = recentMin < support * 0.9985;
      return { confirmed: broke, reason: broke ? 'Support broken down' : null };
    }

    case 'double_bottom': {
      // Resistance = highest point between the two bottoms
      const midSection  = win.slice(Math.floor(N*0.2), Math.floor(N*0.8));
      const resistance  = Math.max(...midSection);
      const broke       = recentMax > resistance * 1.0015;
      return { confirmed: broke, reason: broke ? 'Resistance broken up' : null };
    }

    case 'bull_flag': {
      // Flag = tight consolidation in middle section
      // Breakout = price above the highest point of the flag
      const flagZone    = win.slice(Math.floor(N*0.4), Math.floor(N*0.85));
      const flagHigh    = Math.max(...flagZone);
      const broke       = recentMax > flagHigh * 1.001;
      return { confirmed: broke, reason: broke ? 'Flag broken up' : null };
    }

    case 'cup_handle': {
      // Rim = the two peaks at start and ~60% of the pattern
      const rimLeft  = win[0];
      const rimRight = Math.max(...win.slice(Math.floor(N*0.5), Math.floor(N*0.8)));
      const rim      = Math.max(rimLeft, rimRight);
      const broke    = recentMax > rim * 1.001;
      return { confirmed: broke, reason: broke ? 'Cup rim broken up' : null };
    }

    case 'bull_breakout': {
      // Consolidation high = max of the flat zone (first 80%)
      const consHigh = Math.max(...win.slice(0, Math.floor(N*0.8)));
      const broke    = recentMax > consHigh * 1.001;
      return { confirmed: broke, reason: broke ? 'Breakout confirmed' : null };
    }

    case 'bear_breakdown': {
      const consLow = Math.min(...win.slice(0, Math.floor(N*0.8)));
      const broke   = recentMin < consLow * 0.999;
      return { confirmed: broke, reason: broke ? 'Breakdown confirmed' : null };
    }

    default:
      return { confirmed: true, reason: null };
  }
}

// ── Breakout shape detector ──
// Checks if a price window looks like consolidation → explosive move.
// Returns a bonus 0–0.15 added to Pearson score for breakout-like windows.
function breakoutBonus(win, tmpl) {
  const n       = win.length;
  const cutoff  = Math.floor(n * 0.7);          // first 70% = body, last 30% = breakout
  const body    = win.slice(0, cutoff);
  const tail    = win.slice(cutoff);
  if (body.length < 3 || tail.length < 2) return 0;

  const bodyMn  = Math.min(...body), bodyMx = Math.max(...body);
  const bodyRng = bodyMx - bodyMn;
  const fullRng = Math.max(...win) - Math.min(...win);
  if (fullRng === 0) return 0;

  // Body should be tight (< 35% of full range) — consolidation zone
  const tightness = 1 - (bodyRng / fullRng);
  if (tightness < 0.5) return 0;   // body too wide → not a breakout

  // Tail should move decisively away from body average
  const bodyAvg = body.reduce((s,v)=>s+v,0) / body.length;
  const tailEnd = tail[tail.length - 1];
  const breakMove = Math.abs(tailEnd - bodyAvg) / fullRng;
  if (breakMove < 0.4) return 0;   // tail move too small

  // Template end direction must match actual breakout direction
  const tmplEnd  = tmpl[tmpl.length - 1];
  const tmplStart = tmpl[0];
  const tmplUp   = tmplEnd > tmplStart;
  const priceUp  = tailEnd > bodyAvg;
  if (tmplUp !== priceUp) return 0; // direction mismatch

  return Math.min(0.15, tightness * breakMove * 0.3);
}

function findBestMatch(prices, template) {
  const tmpl = normalize(template.map(y => 1 - y));
  const N    = prices.length;
  const minWin = Math.max(template.length + 2, 8);

  // Window sizes to try: 12% – 65% of total candles
  const ratios   = [0.12, 0.18, 0.25, 0.33, 0.42, 0.52, 0.62, 0.65];
  const winSizes = [...new Set(
    ratios.map(r => Math.round(N * r)).filter(w => w >= minWin && w <= N)
  )];

  // ── PASS 1: Windows that END at the very last candle (daysAgo = 0) ──
  // This is the only thing that matters for actionable signals.
  // Pattern must be finishing RIGHT NOW.
  let tailBest = { score: -1, start: 0, end: N-1, matchPrices: [] };
  for (const wSz of winSizes) {
    const st  = N - wSz;           // always ends at last candle
    if (st < 0) continue;
    const win  = prices.slice(st);
    const winN = resample(normalize(win), tmpl.length);
    const corr = pearson(tmpl, winN) + breakoutBonus(win, tmpl);
    if (corr > tailBest.score) {
      tailBest = { score: Math.min(corr, 1.0), start: st, end: N-1, matchPrices: win };
    }
  }

  // ── PASS 2: Windows ending within last 5 candles (near-tail, "just completing") ──
  let nearBest = { score: -1, start: 0, end: N-1, matchPrices: [] };
  for (const wSz of winSizes) {
    for (let lag = 1; lag <= 5; lag++) {
      const end = N - 1 - lag;
      const st  = end - wSz + 1;
      if (st < 0) continue;
      const win  = prices.slice(st, end + 1);
      const winN = resample(normalize(win), tmpl.length);
      const corr = pearson(tmpl, winN) + breakoutBonus(win, tmpl);
      if (corr > nearBest.score) {
        nearBest = { score: Math.min(corr, 1.0), start: st, end, matchPrices: win };
      }
    }
  }

  // ── PASS 3: Full history scan (historical reference only) ──
  let histBest = { score: -1, start: 0, end: N-1, matchPrices: [] };
  for (const wSz of winSizes) {
    for (let st = 0; st <= N - wSz; st++) {
      const win  = prices.slice(st, st + wSz);
      const winN = resample(normalize(win), tmpl.length);
      const corr = pearson(tmpl, winN) + breakoutBonus(win, tmpl);
      const end  = st + wSz - 1;
      if (corr > histBest.score) {
        histBest = { score: Math.min(corr, 1.0), start: st, end, matchPrices: win };
      }
    }
  }

  // Pick the best from tail first, then near, then hist
  // isRecent = pattern is ending at or within 5 candles of today
  const daysAgoTail = 0;
  const daysAgoNear = N - 1 - nearBest.end;

  let chosen, daysAgo, isRecent;

  if (tailBest.score >= nearBest.score && tailBest.score >= 0) {
    chosen   = tailBest;
    daysAgo  = 0;
    isRecent = true;
  } else if (nearBest.score >= tailBest.score && nearBest.score >= 0) {
    // Use near only if it scores meaningfully better than tail
    if (nearBest.score > tailBest.score + 0.04) {
      chosen   = nearBest;
      daysAgo  = daysAgoNear;
      isRecent = true;
    } else {
      chosen   = tailBest;
      daysAgo  = 0;
      isRecent = true;
    }
  } else {
    chosen   = histBest;
    daysAgo  = N - 1 - histBest.end;
    isRecent = false;
  }

  // If the tail/near score is way below hist, mark as historical
  if (histBest.score > chosen.score + 0.15) {
    chosen   = histBest;
    daysAgo  = N - 1 - histBest.end;
    isRecent = false;
  }

  return { ...chosen, daysAgo, isRecent };
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

// GET /api/ticker — fast batch fetch of indices + popular stocks for the marquee
const TICKER_SYMBOLS = [
  // Indices
  { s:'^NSEI',      l:'NIFTY 50'   },
  { s:'^NSEBANK',   l:'BANK NIFTY' },
  { s:'^CNXIT',     l:'NIFTY IT'   },
  // Popular NSE stocks
  { s:'RELIANCE.NS', l:'RELIANCE' },
  { s:'TCS.NS',      l:'TCS'      },
  { s:'HDFCBANK.NS', l:'HDFC Bank'},
  { s:'INFY.NS',     l:'Infosys'  },
  { s:'ICICIBANK.NS',l:'ICICI Bank'},
  { s:'SBIN.NS',     l:'SBI'      },
  { s:'BAJFINANCE.NS',l:'Bajaj Fin'},
  { s:'TATAMOTORS.NS',l:'Tata Motors'},
  { s:'WIPRO.NS',    l:'Wipro'    },
  { s:'SUNPHARMA.NS',l:'Sun Pharma'},
  // Crypto
  { s:'BTC-USD',  l:'BTC'  },
  { s:'ETH-USD',  l:'ETH'  },
  { s:'SOL-USD',  l:'SOL'  },
  { s:'BNB-USD',  l:'BNB'  },
];

// Cache ticker data for 60 seconds so repeated visits don't hammer Yahoo
// Cache ticker data — 90 seconds
let tickerCache     = null;
let tickerCacheTime = 0;

// Fetch a single ticker symbol with a hard 6s timeout
function fetchTickerSymbol(sym) {
  return new Promise((resolve) => {
    const url = `https://query1.finance.yahoo.com/v8/finance/chart/${encodeURIComponent(sym.s)}?interval=1d&range=5d`;
    const opts = {
      headers: {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120',
        'Accept': 'application/json',
      },
      timeout: 6000,
    };
    const req = https.get(url, opts, (resp) => {
      let data = '';
      resp.on('data', c => data += c);
      resp.on('end', () => {
        try {
          const json = JSON.parse(data);
          const r    = json?.chart?.result?.[0];
          if (!r) return resolve(null);

          const meta   = r.meta || {};
          const closes = r.indicators.quote[0].close.filter(c => c != null);
          if (!closes.length) return resolve(null);

          const last = meta.regularMarketPrice || closes[closes.length - 1];

          // Use Yahoo's own change percent — most accurate, handles pre/post market correctly
          let change = 0;
          if (meta.regularMarketChangePercent != null && meta.regularMarketChangePercent !== 0) {
            change = parseFloat(meta.regularMarketChangePercent.toFixed(2));
          } else if (meta.chartPreviousClose && meta.chartPreviousClose !== 0 && meta.chartPreviousClose !== last) {
            change = parseFloat(((last - meta.chartPreviousClose) / meta.chartPreviousClose * 100).toFixed(2));
          } else if (closes.length >= 2) {
            // Find last two distinct closes
            let prev = null;
            for (let i = closes.length - 2; i >= 0; i--) {
              if (closes[i] != null && closes[i] !== last) { prev = closes[i]; break; }
            }
            if (prev) change = parseFloat(((last - prev) / prev * 100).toFixed(2));
          }

          resolve({
            symbol: sym.s,
            label:  sym.l,
            price:  parseFloat(last.toFixed(2)),
            change,
          });
        } catch { resolve(null); }
      });
    });
    req.on('error',   () => resolve(null));
    req.on('timeout', () => { req.destroy(); resolve(null); });
  });
}

async function handleTickerAPI(res) {
  const now = Date.now();
  // Serve cache if fresh (90 seconds)
  if (tickerCache && tickerCache.items.length > 0 && now - tickerCacheTime < 90000) {
    return sendJSON(res, 200, tickerCache);
  }

  // Fire all requests in parallel — much faster than sequential
  const settled = await Promise.all(TICKER_SYMBOLS.map(sym => fetchTickerSymbol(sym)));
  const results = settled.filter(Boolean);

  if (results.length > 0) {
    tickerCache     = { items: results, ts: now };
    tickerCacheTime = now;
  }

  sendJSON(res, 200, tickerCache || { items: [], ts: now });
}

// ─── Details: News + Fundamentals ──────────────────────────────────────────────
const detailsCache = new Map();

function fetchText(url, extraHeaders = {}) {
  return new Promise((resolve, reject) => {
    const opts = {
      headers: {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/121',
        'Accept': '*/*',
        'Accept-Language': 'en-US,en;q=0.9',
        'Accept-Encoding': 'identity',
        'Cache-Control': 'no-cache',
        ...extraHeaders,
      },
      timeout: 10000,
    };
    const req = https.get(url, opts, (res) => {
      if (res.statusCode === 301 || res.statusCode === 302) {
        return fetchText(res.headers.location, extraHeaders).then(resolve).catch(reject);
      }
      let d = '';
      res.on('data', c => d += c);
      res.on('end', () => resolve({ status: res.statusCode, text: d, headers: res.headers }));
    });
    req.on('error', reject);
    req.on('timeout', () => { req.destroy(); reject(new Error('Timeout')); });
  });
}

function fmtBig(n) {
  if (!n || isNaN(n)) return null;
  if (Math.abs(n) >= 1e12) return (n / 1e12).toFixed(2) + 'T';
  if (Math.abs(n) >= 1e9)  return (n / 1e9).toFixed(2)  + 'B';
  if (Math.abs(n) >= 1e6)  return (n / 1e6).toFixed(2)  + 'M';
  if (Math.abs(n) >= 1e3)  return (n / 1e3).toFixed(2)  + 'K';
  return n.toLocaleString();
}

// ── Google News RSS — always works, no auth, no rate limit ──
async function fetchGoogleNews(query) {
  try {
    const url  = `https://news.google.com/rss/search?q=${encodeURIComponent(query + ' stock')}&hl=en-IN&gl=IN&ceid=IN:en`;
    const resp = await fetchText(url);
    if (resp.status !== 200 || !resp.text.includes('<item>')) return [];
    const items = [];
    const rx    = /<item>([\s\S]*?)<\/item>/g;
    let m;
    while ((m = rx.exec(resp.text)) !== null) {
      const b      = m[1];
      const get    = (t) => { const r = new RegExp(`<${t}[^>]*>(?:<!\\[CDATA\\[)?([\\s\\S]*?)(?:\\]\\]>)?</${t}>`); const x = r.exec(b); return x ? x[1].trim() : null; };
      const title  = get('title');
      const link   = get('link');
      const pubDate= get('pubDate');
      const src    = /<source[^>]*>([^<]*)<\/source>/.exec(b)?.[1] || 'Google News';
      if (title && link) items.push({
        title,
        link,
        publisher: src,
        time: pubDate ? Math.floor(new Date(pubDate).getTime() / 1000) : null,
      });
    }
    return items.slice(0, 12);
  } catch (e) {
    return [];
  }
}

// ── NSE India API — free, official, no auth for basic quote ──
async function fetchNSEFundamentals(symbol) {
  try {
    // Strip .NS suffix
    const nse = symbol.replace('.NS', '').replace('.BO', '');
    const url  = `https://www.nseindia.com/api/quote-equity?symbol=${encodeURIComponent(nse)}`;
    const resp = await fetchText(url, {
      'Referer':     'https://www.nseindia.com/',
      'Accept':      'application/json',
      'X-Requested-With': 'XMLHttpRequest',
    });
    if (resp.status !== 200) return null;
    const json = JSON.parse(resp.text);
    const info = json?.industryInfo || {};
    const pd   = json?.priceInfo    || {};
    const md   = json?.metadata     || {};
    const fi   = json?.securityInfo || {};
    const f    = {};
    if (md.companyName)                f.name         = md.companyName;
    if (info.sector)                   f.sector       = info.sector;
    if (info.industry)                 f.industry     = info.industry;
    if (pd.weekHighLow?.max)           f.week52High   = pd.weekHighLow.max.toString();
    if (pd.weekHighLow?.min)           f.week52Low    = pd.weekHighLow.min.toString();
    if (pd.close)                      f.price        = pd.close;
    if (pd.pChange !== undefined)      f.changePercent = pd.pChange.toFixed(2) + '%';
    if (fi.issuedSize)                 f.sharesOut    = fmtBig(fi.issuedSize);
    if (md.pdSectorPe)                 f.sectorPE     = md.pdSectorPe.toString();
    if (md.pdSymbolPe)                 f.peRatio      = md.pdSymbolPe.toString();
    return Object.keys(f).length > 0 ? f : null;
  } catch (e) {
    return null;
  }
}

// ── CoinGecko — free, no API key for basic data ──
const COINGECKO_IDS = {
  'BTC-USD':'bitcoin','ETH-USD':'ethereum','BNB-USD':'binancecoin',
  'SOL-USD':'solana','XRP-USD':'ripple','ADA-USD':'cardano',
  'AVAX-USD':'avalanche-2','DOGE-USD':'dogecoin','DOT-USD':'polkadot',
  'MATIC-USD':'matic-network','SHIB-USD':'shiba-inu','TRX-USD':'tron',
  'LTC-USD':'litecoin','LINK-USD':'chainlink','ATOM-USD':'cosmos',
  'UNI-USD':'uniswap','XLM-USD':'stellar','BCH-USD':'bitcoin-cash',
  'APT-USD':'aptos','ARB-USD':'arbitrum','AAVE-USD':'aave',
  'MKR-USD':'maker','SNX-USD':'havven','CRV-USD':'curve-dao-token',
  'COMP-USD':'compound-governance-token','SUSHI-USD':'sushi',
  'YFI-USD':'yearn-finance','LDO-USD':'lido-dao','NEAR-USD':'near',
  'FTM-USD':'fantom','ALGO-USD':'algorand','ICP-USD':'internet-computer',
  'HBAR-USD':'hedera-hashgraph','OP-USD':'optimism','SUI-USD':'sui',
};

async function fetchCoinGeckoFundamentals(symbol) {
  const id = COINGECKO_IDS[symbol];
  if (!id) return null;
  try {
    const url  = `https://api.coingecko.com/api/v3/coins/${id}?localization=false&tickers=false&community_data=false&developer_data=false`;
    const resp = await fetchText(url, { 'Accept': 'application/json' });
    if (resp.status !== 200) return null;
    const d  = JSON.parse(resp.text);
    const md = d.market_data || {};
    const f  = {};
    if (d.name)                                    f.name          = d.name;
    if (d.categories?.length)                      f.sector        = d.categories.slice(0,2).join(', ');
    if (md.market_cap?.usd)                        f.marketCap     = fmtBig(md.market_cap.usd);
    if (md.current_price?.usd)                     f.price         = '$' + md.current_price.usd.toLocaleString();
    if (md.price_change_percentage_24h != null)    f.change24h     = md.price_change_percentage_24h.toFixed(2) + '%';
    if (md.high_24h?.usd)                          f.high24h       = '$' + md.high_24h.usd.toLocaleString();
    if (md.low_24h?.usd)                           f.low24h        = '$' + md.low_24h.usd.toLocaleString();
    if (md.ath?.usd)                               f.allTimeHigh   = '$' + md.ath.usd.toLocaleString();
    if (md.atl?.usd)                               f.allTimeLow    = '$' + md.atl.usd.toLocaleString();
    if (md.total_volume?.usd)                      f.volume24h     = fmtBig(md.total_volume.usd);
    if (md.circulating_supply)                     f.circSupply    = fmtBig(md.circulating_supply);
    if (md.total_supply)                           f.totalSupply   = fmtBig(md.total_supply);
    if (md.price_change_percentage_7d_in_currency?.usd != null) f.change7d = md.price_change_percentage_7d_in_currency.usd.toFixed(2) + '%';
    if (md.price_change_percentage_30d_in_currency?.usd != null) f.change30d = md.price_change_percentage_30d_in_currency.usd.toFixed(2) + '%';
    if (d.description?.en)                         f.description   = d.description.en.replace(/<[^>]+>/g,'').slice(0, 300) + '…';
    return f;
  } catch (e) {
    return null;
  }
}

// ── Yahoo Finance v7 as last-resort fallback ──
async function fetchYahooQuote(symbol) {
  try {
    // Try query2 first (different IP pool, less rate-limited)
    for (const host of ['query2.finance.yahoo.com', 'query1.finance.yahoo.com']) {
      const url  = `https://${host}/v7/finance/quote?symbols=${encodeURIComponent(symbol)}&fields=trailingPE,priceToBook,marketCap,fiftyTwoWeekHigh,fiftyTwoWeekLow,epsTrailingTwelveMonths,trailingAnnualDividendYield,averageDailyVolume10Day,regularMarketVolume,sector,industry,shortName`;
      const resp = await fetchText(url);
      if (resp.status === 200) {
        const json = JSON.parse(resp.text);
        const q    = json?.quoteResponse?.result?.[0];
        if (!q) continue;
        const f = {};
        if (q.shortName)                       f.name          = q.shortName;
        if (q.marketCap)                       f.marketCap     = fmtBig(q.marketCap);
        if (q.trailingPE)                      f.peRatio       = q.trailingPE.toFixed(2);
        if (q.priceToBook)                     f.pbRatio       = q.priceToBook.toFixed(2);
        if (q.epsTrailingTwelveMonths)         f.eps           = q.epsTrailingTwelveMonths.toFixed(2);
        if (q.fiftyTwoWeekHigh)                f.week52High    = q.fiftyTwoWeekHigh.toFixed(2);
        if (q.fiftyTwoWeekLow)                 f.week52Low     = q.fiftyTwoWeekLow.toFixed(2);
        if (q.averageDailyVolume10Day)         f.avgVolume     = fmtBig(q.averageDailyVolume10Day);
        if (q.regularMarketVolume)             f.volume        = fmtBig(q.regularMarketVolume);
        if (q.trailingAnnualDividendYield)     f.dividendYield = (q.trailingAnnualDividendYield * 100).toFixed(2) + '%';
        if (q.sector)                          f.sector        = q.sector;
        if (q.industry)                        f.industry      = q.industry;
        return f;
      }
    }
  } catch (e) {}
  return null;
}

async function handleDetailsAPI(query, res) {
  const { symbol } = query;
  if (!symbol) return sendJSON(res, 400, { error: 'symbol required' });

  const cached = detailsCache.get(symbol);
  if (cached && Date.now() - cached.ts < 300000) return sendJSON(res, 200, cached.data);

  const isCrypto = symbol.includes('-USD');
  const result   = { news: [], fundamentals: {} };
  const fmtB = (n) => {
    if (!n || isNaN(n)) return null;
    if (n >= 1e12) return (n/1e12).toFixed(2)+'T';
    if (n >= 1e9)  return (n/1e9).toFixed(2)+'B';
    if (n >= 1e6)  return (n/1e6).toFixed(2)+'M';
    if (n >= 1e3)  return (n/1e3).toFixed(1)+'K';
    return n.toLocaleString();
  };

  // ── STEP 1: Chart meta (always works) ──
  // Gives us: 52w high/low, day high/low, volume, current price, longName
  try {
    const r    = await fetchText(`https://query1.finance.yahoo.com/v8/finance/chart/${encodeURIComponent(symbol)}?interval=1d&range=2d`);
    const meta = JSON.parse(r.text)?.chart?.result?.[0]?.meta || {};
    if (meta.fiftyTwoWeekHigh)     result.fundamentals.week52High   = meta.fiftyTwoWeekHigh.toFixed(2);
    if (meta.fiftyTwoWeekLow)      result.fundamentals.week52Low    = meta.fiftyTwoWeekLow.toFixed(2);
    if (meta.regularMarketDayHigh) result.fundamentals.dayHigh      = meta.regularMarketDayHigh.toFixed(2);
    if (meta.regularMarketDayLow)  result.fundamentals.dayLow       = meta.regularMarketDayLow.toFixed(2);
    if (meta.regularMarketVolume)  result.fundamentals.volume       = fmtB(meta.regularMarketVolume);
    if (meta.regularMarketPrice)   result.fundamentals.price        = meta.regularMarketPrice;
    if (meta.chartPreviousClose)   result.fundamentals.prevClose    = meta.chartPreviousClose.toFixed(2);
    if (meta.currency)             result.fundamentals.currency     = meta.currency;
    if (meta.exchangeName)         result.fundamentals.exchange     = meta.exchangeName;
    if (meta.longName)             result.fundamentals.name         = meta.longName;
  } catch(e) { console.log('[details] chart meta error:', e.message); }

  // ── STEP 2a: NSE India API for Indian stocks ──
  // Returns: companyName, industry, PE, 52w high/low, market cap, more
  if (!isCrypto) {
    try {
      const nse  = symbol.replace('.NS','').replace('.BO','');
      const r    = await fetchText(
        `https://www.nseindia.com/api/quote-equity?symbol=${encodeURIComponent(nse)}`,
        { 'Referer': 'https://www.nseindia.com/', 'Accept': 'application/json', 'X-Requested-With': 'XMLHttpRequest' }
      );
      if (r.status === 200) {
        const d  = JSON.parse(r.text);
        const info = d.info       || {};
        const pi   = d.priceInfo  || {};
        const md   = d.metadata   || {};
        const si   = d.securityInfo || {};

        if (info.companyName)              result.fundamentals.name         = info.companyName;
        if (info.industry)                 result.fundamentals.industry     = info.industry;
        if (md.pdSectorInd)                result.fundamentals.sector       = md.pdSectorInd;
        if (md.pdSymbolPe)                 result.fundamentals.peRatio      = parseFloat(md.pdSymbolPe).toFixed(2);
        if (md.pdSectorPe)                 result.fundamentals.sectorPE     = parseFloat(md.pdSectorPe).toFixed(2);
        if (pi.weekHighLow?.max)           result.fundamentals.week52High   = pi.weekHighLow.max.toFixed ? pi.weekHighLow.max.toFixed(2) : pi.weekHighLow.max;
        if (pi.weekHighLow?.min)           result.fundamentals.week52Low    = pi.weekHighLow.min.toFixed ? pi.weekHighLow.min.toFixed(2) : pi.weekHighLow.min;
        if (pi.vwap)                       result.fundamentals.vwap         = parseFloat(pi.vwap).toFixed(2);
        if (si.issuedSize)                 result.fundamentals.sharesOut    = fmtB(si.issuedSize);
        if (pi.pChange !== undefined)      result.fundamentals.changePercent = pi.pChange.toFixed(2) + '%';

        // Market cap = price × shares
        if (result.fundamentals.price && si.issuedSize) {
          result.fundamentals.marketCap = fmtB(result.fundamentals.price * si.issuedSize);
        }

        // Face value, listing date from securityInfo
        if (si.faceVal)                    result.fundamentals.faceValue    = '₹' + si.faceVal;

        console.log('[details] NSE OK for', nse, '- fields:', Object.keys(result.fundamentals).join(', '));
      }
    } catch(e) { console.log('[details] NSE error:', e.message); }
  }

  // ── STEP 2b: CoinGecko for crypto ──
  if (isCrypto) {
    try {
      const id   = COINGECKO_IDS[symbol];
      if (id) {
        const r = await fetchText(
          `https://api.coingecko.com/api/v3/coins/${id}?localization=false&tickers=false&community_data=false&developer_data=false`,
          { 'Accept': 'application/json' }
        );
        if (r.status === 200) {
          const d  = JSON.parse(r.text);
          const md = d.market_data || {};
          const f  = result.fundamentals;
          if (d.name)                                     f.name        = d.name;
          if (d.categories?.length)                       f.sector      = d.categories.slice(0,2).join(', ');
          if (md.market_cap?.usd)                         f.marketCap   = fmtB(md.market_cap.usd);
          if (md.price_change_percentage_24h != null)     f.change24h   = md.price_change_percentage_24h.toFixed(2)+'%';
          if (md.price_change_percentage_7d_in_currency?.usd != null) f.change7d = md.price_change_percentage_7d_in_currency.usd.toFixed(2)+'%';
          if (md.price_change_percentage_30d_in_currency?.usd != null) f.change30d = md.price_change_percentage_30d_in_currency.usd.toFixed(2)+'%';
          if (md.high_24h?.usd)                           f.high24h     = '$'+md.high_24h.usd.toLocaleString();
          if (md.low_24h?.usd)                            f.low24h      = '$'+md.low_24h.usd.toLocaleString();
          if (md.ath?.usd)                                f.allTimeHigh = '$'+md.ath.usd.toLocaleString();
          if (md.atl?.usd)                                f.allTimeLow  = '$'+md.atl.usd.toLocaleString();
          if (md.total_volume?.usd)                       f.volume24h   = fmtB(md.total_volume.usd);
          if (md.circulating_supply)                      f.circSupply  = fmtB(md.circulating_supply);
          if (md.total_supply)                            f.totalSupply = fmtB(md.total_supply);
          if (md.max_supply)                              f.maxSupply   = fmtB(md.max_supply);
          if (d.description?.en)                         f.description = d.description.en.replace(/<[^>]+>/g,'').slice(0,300)+'…';
          console.log('[details] CoinGecko OK for', id);
        }
      }
    } catch(e) { console.log('[details] CoinGecko error:', e.message); }
  }

  // ── STEP 3: Google News RSS ──
  try {
    const name   = result.fundamentals.name || symbol.replace('.NS','').replace('.BO','').replace('-USD','');
    const q      = isCrypto ? name + ' cryptocurrency' : name + ' stock NSE';
    const rssUrl = `https://news.google.com/rss/search?q=${encodeURIComponent(q)}&hl=en-IN&gl=IN&ceid=IN:en`;
    const r      = await fetchText(rssUrl);

    if (r.status === 200 && r.text.includes('<item>')) {
      // Split on <item> boundaries — safer than regex on full doc
      const blocks = r.text.split('<item>').slice(1);

      for (const block of blocks) {
        if (result.news.length >= 12) break;

        // Title — strip CDATA wrapper if present
        const titleMatch = /<title[^>]*>(?:<!\[CDATA\[)?([\s\S]*?)(?:\]\]>)?<\/title>/i.exec(block);
        const title      = titleMatch ? titleMatch[1].trim() : null;

        // Link — Google News sometimes uses <link> without closing tag
        // Try multiple patterns
        let link = null;
        const linkPatterns = [
          /<link>([^<]+)<\/link>/i,          // standard closing tag
          /<link\s*\/?>\s*([hH][tT][tT][pP][^\s<]+)/i,  // self-closing then URL
          /<guid[^>]*>([^<]+)<\/guid>/i,     // fallback: guid often has the URL
        ];
        for (const pat of linkPatterns) {
          const m = pat.exec(block);
          if (m && m[1] && m[1].startsWith('http')) { link = m[1].trim(); break; }
        }

        // pubDate
        const pubMatch = /<pubDate>([^<]+)<\/pubDate>/i.exec(block);
        const pub      = pubMatch ? pubMatch[1].trim() : null;

        // Source / publisher
        const srcMatch = /<source[^>]*>([^<]+)<\/source>/i.exec(block);
        const src      = srcMatch ? srcMatch[1].trim() : 'Google News';

        if (title && link) {
          result.news.push({
            title,
            link,
            publisher: src,
            time: pub ? Math.floor(new Date(pub).getTime() / 1000) : null,
          });
        }
      }
      console.log(`[details] Google News: ${result.news.length} articles for "${name}"`);
    } else {
      console.log('[details] Google News status:', r.status, 'has items:', r.text.includes('<item>'));
    }
  } catch(e) { console.log('[details] news error:', e.message); }

  detailsCache.set(symbol, { data: result, ts: Date.now() });
  sendJSON(res, 200, result);
}
async function handleScanAPI(body, res) {
  let parsed;
  try { parsed = JSON.parse(body); } catch { return sendJSON(res, 400, { error: 'Invalid JSON' }); }

  const { symbols, timeframe, template, threshold, recency, patternType } = parsed;
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
        const daysAgo = match.daysAgo !== undefined ? match.daysAgo : (data.prices.length - 1 - match.end);

        // ── Pattern-specific confirmation check ──
        // For preset patterns: only include if the technical condition is met
        // For freehand drawings (patternType = null): include all recent matches
        let confirmed = true, confirmReason = null;
        if (patternType && match.matchPrices && match.matchPrices.length > 4) {
          const chk = confirmPattern(match.matchPrices, patternType);
          confirmed     = chk.confirmed;
          confirmReason = chk.reason;
          // Strict freshness for confirmed patterns: must end within last 3 candles
          if (confirmed && daysAgo > 3) confirmed = false;
        }

        // Skip unconfirmed preset patterns entirely
        if (patternType && !confirmed) continue;

        results.push({
          symbol:        sym.symbol,
          name:          sym.name,
          score:         parseFloat(match.score.toFixed(4)),
          price:         data.price,
          change:        data.change,
          prices:        data.prices,
          dates:         data.dates,
          matchStart:    match.start,
          matchEnd:      match.end,
          matchPrices:   match.matchPrices,
          daysAgo,
          isRecent:      match.isRecent === true,
          timeframe:     data.timeframe,
          confirmed,
          confirmReason,
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

  // Debug test — hit /api/test?symbol=TCS.NS to see raw responses from each source
  if (pathname === '/api/test' && req.method === 'GET') {
    const sym = parsed.query.symbol || 'TCS.NS';
    (async () => {
      const out = {};
      try { const r = await fetchText(`https://query1.finance.yahoo.com/v8/finance/chart/${encodeURIComponent(sym)}?interval=1d&range=2d`); const j = JSON.parse(r.text); out.chart = { status: r.status, meta_keys: Object.keys(j?.chart?.result?.[0]?.meta||{}) }; } catch(e) { out.chart = { error: e.message }; }
      try { const r = await fetchText(`https://query1.finance.yahoo.com/v7/finance/quote?symbols=${encodeURIComponent(sym)}`); out.v7q1 = { status: r.status, preview: r.text.slice(0,200) }; } catch(e) { out.v7q1 = { error: e.message }; }
      try { const r = await fetchText(`https://query2.finance.yahoo.com/v7/finance/quote?symbols=${encodeURIComponent(sym)}`); out.v7q2 = { status: r.status, preview: r.text.slice(0,200) }; } catch(e) { out.v7q2 = { error: e.message }; }
      try { const nse = sym.replace('.NS','').replace('.BO',''); const r = await fetchText(`https://www.nseindia.com/api/quote-equity?symbol=${encodeURIComponent(nse)}`, {'Referer':'https://www.nseindia.com/','Accept':'application/json'}); out.nse = { status: r.status, preview: r.text.slice(0,200) }; } catch(e) { out.nse = { error: e.message }; }
      try { const r = await fetchText(`https://news.google.com/rss/search?q=${encodeURIComponent(sym+' stock')}&hl=en-IN&gl=IN&ceid=IN:en`); out.gnews = { status: r.status, items: (r.text.match(/<item>/g)||[]).length }; } catch(e) { out.gnews = { error: e.message }; }
      try { const r = await fetchText('https://api.coingecko.com/api/v3/simple/price?ids=bitcoin&vs_currencies=usd&include_market_cap=true'); out.coingecko = { status: r.status, preview: r.text.slice(0,150) }; } catch(e) { out.coingecko = { error: e.message }; }
      sendJSON(res, 200, out);
    })();
    return;
  }

  // Ticker — batch price/change for marquee
  if (pathname === '/api/ticker' && req.method === 'GET') {
    return handleTickerAPI(res);
  }

  // Stock details — news + fundamentals
  if (pathname === '/api/details' && req.method === 'GET') {
    return handleDetailsAPI(parsed.query, res);
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
