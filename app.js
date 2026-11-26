// Safe Storage Wrappers (prevents SecurityError in restricted file:// or private mode contexts)
const _memStore = {};
function safeGetLocal(key) {
  try { return window["localStorage"].getItem(key); } catch (_) { return _memStore["L_" + key] ?? null; }
}
function safeSetLocal(key, val) {
  try { window["localStorage"].setItem(key, val); } catch (_) { _memStore["L_" + key] = String(val); }
}
function safeRemoveLocal(key) {
  try { window["localStorage"].removeItem(key); } catch (_) { delete _memStore["L_" + key]; }
}
function safeGetSession(key) {
  try { return window["sessionStorage"].getItem(key); } catch (_) { return _memStore["S_" + key] ?? null; }
}
function safeSetSession(key, val) {
  try { window["sessionStorage"].setItem(key, val); } catch (_) { _memStore["S_" + key] = String(val); }
}
function safeRemoveSession(key) {
  try { window["sessionStorage"].removeItem(key); } catch (_) { delete _memStore["S_" + key]; }
}

// 2-Step Login Gate Engine (SHA-256 Password + RFC 6238 TOTP 6-Digit OTP for iPhone Passwords / Authenticator)
const GATE_SESSION_KEY = "TMC_GATE_AUTHENTICATED_V1";
const GATE_PASS_HASH_KEY = "TMC_GATE_PASS_SHA256_V1";
const GATE_TOTP_SECRET_KEY = "TMC_GATE_TOTP_SECRET_V1";
const GATE_2FA_ENABLED_KEY = "TMC_GATE_2FA_ENABLED_V1";
let pendingTotpCandidateSecret = "";
let failedLoginAttempts = 0;
let loginLockoutUntil = 0;

function is2faEnabled() {
  return safeGetLocal(GATE_2FA_ENABLED_KEY) === "true" && Boolean(safeGetLocal(GATE_TOTP_SECRET_KEY));
}
const BASE32_ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567";

// Pure JS SHA-256 implementation (works even on file:// or non-HTTPS origins where crypto.subtle may be restricted)
function pureJsSha256Hex(asciiStr) {
  function rightRotate(value, amount) {
    return (value >>> amount) | (value << (32 - amount));
  }
  const mathPow = Math.pow;
  const maxWord = mathPow(2, 32);
  let i, j;
  let result = "";
  const words = [];
  const asciiBitLength = asciiStr.length * 8;
  let hash = pureJsSha256Hex.h = pureJsSha256Hex.h || [];
  const k = pureJsSha256Hex.k = pureJsSha256Hex.k || [];
  let primeCounter = k.length;
  const isComposite = {};
  for (let candidate = 2; primeCounter < 64; candidate++) {
    if (!isComposite[candidate]) {
      for (i = 0; i < 313; i += candidate) {
        isComposite[i] = candidate;
      }
      hash[primeCounter] = (mathPow(candidate, 0.5) * maxWord) | 0;
      k[primeCounter++] = (mathPow(candidate, 1 / 3) * maxWord) | 0;
    }
  }
  const utf8Str = unescape(encodeURIComponent(String(asciiStr)));
  const utf8BitLength = utf8Str.length * 8;
  for (i = 0; i < utf8Str.length; i++) {
    words[i >> 2] |= utf8Str.charCodeAt(i) << ((3 - i) % 4) * 8;
  }
  words[words.length] = (0x80) << ((3 - utf8Str.length) % 4) * 8;
  if ((words.length - 1) % 16 > 14) {
    while (words.length % 16 !== 0) words.push(0);
  }
  while (words.length % 16 !== 14) words.push(0);
  words.push(utf8BitLength >>> 0);
  words.push((utf8BitLength / maxWord) | 0);

  for (j = 0; j < words.length; j += 16) {
    const w = words.slice(j, j + 16);
    const oldHash = hash.slice(0, 8);
    for (i = 0; i < 64; i++) {
      if (i >= 16) {
        const s0 = rightRotate(w[i - 15], 7) ^ rightRotate(w[i - 15], 18) ^ (w[i - 15] >>> 3);
        const s1 = rightRotate(w[i - 2], 17) ^ rightRotate(w[i - 2], 19) ^ (w[i - 2] >>> 10);
        w[i] = (w[i - 16] + s0 + w[i - 7] + s1) | 0;
      }
      const ch = (oldHash[4] & oldHash[5]) ^ (~oldHash[4] & oldHash[6]);
      const temp1 = (oldHash[7] + (rightRotate(oldHash[4], 6) ^ rightRotate(oldHash[4], 11) ^ rightRotate(oldHash[4], 25)) + ch + k[i] + w[i]) | 0;
      const maj = (oldHash[0] & oldHash[1]) ^ (oldHash[0] & oldHash[2]) ^ (oldHash[1] & oldHash[2]);
      const temp2 = ((rightRotate(oldHash[0], 2) ^ rightRotate(oldHash[0], 13) ^ rightRotate(oldHash[0], 22)) + maj) | 0;
      oldHash.pop();
      oldHash.unshift((temp1 + temp2) | 0);
      oldHash[4] = (oldHash[4] + temp1) | 0;
    }
    for (i = 0; i < 8; i++) {
      hash[i] = (hash[i] + oldHash[i]) | 0;
    }
  }
  for (i = 0; i < 8; i++) {
    for (j = 3; j + 1; j--) {
      const b = (hash[i] >> (j * 8)) & 255;
      result += ((b < 16) ? 0 : "") + b.toString(16);
    }
  }
  // Reset cached state for subsequent calls
  pureJsSha256Hex.h = null;
  return result;
}

async function sha256Hex(text) {
  const str = String(text ?? "");
  try {
    if (window.crypto && window.crypto.subtle && typeof window.crypto.subtle.digest === "function") {
      const enc = new TextEncoder();
      const buf = await window.crypto.subtle.digest("SHA-256", enc.encode(str));
      return Array.from(new Uint8Array(buf)).map(b => b.toString(16).padStart(2, "0")).join("");
    }
  } catch (_) {}
  return pureJsSha256Hex(str);
}

function generateBase32Secret(length = 16) {
  const arr = new Uint8Array(length);
  if (window.crypto && typeof window.crypto.getRandomValues === "function") {
    window.crypto.getRandomValues(arr);
  } else {
    for (let i = 0; i < length; i++) arr[i] = Math.floor(Math.random() * 256);
  }
  let out = "";
  for (let i = 0; i < length; i++) {
    out += BASE32_ALPHABET[arr[i] % 32];
  }
  return out;
}

function base32ToBytes(base32) {
  const clean = String(base32 || "").toUpperCase().replace(/[^A-Z2-7]/g, "");
  let bits = 0;
  let value = 0;
  const bytes = [];
  for (let i = 0; i < clean.length; i++) {
    const idx = BASE32_ALPHABET.indexOf(clean[i]);
    if (idx === -1) continue;
    value = (value << 5) | idx;
    bits += 5;
    if (bits >= 8) {
      bytes.push((value >>> (bits - 8)) & 0xff);
      bits -= 8;
    }
  }
  return new Uint8Array(bytes);
}

function pureJsHmacSha1(keyBytes, msgBytes) {
  function rol(num, cnt) { return (num << cnt) | (num >>> (32 - cnt)); }
  function sha1(bytes) {
    const ml = bytes.length * 8;
    const padded = [...bytes, 0x80];
    while (padded.length % 64 !== 56) padded.push(0x00);
    const hi = Math.floor(ml / 0x100000000);
    const lo = ml >>> 0;
    for (let i = 3; i >= 0; i--) padded.push((hi >>> (i * 8)) & 0xff);
    for (let i = 3; i >= 0; i--) padded.push((lo >>> (i * 8)) & 0xff);

    let h0 = 0x67452301, h1 = 0xefcdab89, h2 = 0x98badcfe, h3 = 0x10325476, h4 = 0xc3d2e1f0;
    for (let offset = 0; offset < padded.length; offset += 64) {
      const w = new Array(80);
      for (let t = 0; t < 16; t++) {
        w[t] = ((padded[offset + t * 4] << 24) | (padded[offset + t * 4 + 1] << 16) | (padded[offset + t * 4 + 2] << 8) | padded[offset + t * 4 + 3]) >>> 0;
      }
      for (let t = 16; t < 80; t++) {
        w[t] = rol((w[t - 3] ^ w[t - 8] ^ w[t - 14] ^ w[t - 16]) >>> 0, 1) >>> 0;
      }
      let a = h0, b = h1, c = h2, d = h3, e = h4;
      for (let t = 0; t < 80; t++) {
        let f, k;
        if (t < 20) { f = (b & c) | ((~b) & d); k = 0x5a827999; }
        else if (t < 40) { f = b ^ c ^ d; k = 0x6ed9eba1; }
        else if (t < 60) { f = (b & c) | (b & d) | (c & d); k = 0x8f1bbcdc; }
        else { f = b ^ c ^ d; k = 0xca62c1d6; }
        const temp = (rol(a, 5) + f + e + k + w[t]) >>> 0;
        e = d; d = c; c = rol(b, 30) >>> 0; b = a; a = temp;
      }
      h0 = (h0 + a) >>> 0; h1 = (h1 + b) >>> 0; h2 = (h2 + c) >>> 0; h3 = (h3 + d) >>> 0; h4 = (h4 + e) >>> 0;
    }
    const out = new Uint8Array(20);
    [h0, h1, h2, h3, h4].forEach((hv, idx) => {
      out[idx * 4] = (hv >>> 24) & 0xff;
      out[idx * 4 + 1] = (hv >>> 16) & 0xff;
      out[idx * 4 + 2] = (hv >>> 8) & 0xff;
      out[idx * 4 + 3] = hv & 0xff;
    });
    return out;
  }
  const blockSize = 64;
  let k = Array.from(keyBytes);
  if (k.length > blockSize) k = Array.from(sha1(k));
  while (k.length < blockSize) k.push(0x00);
  const ipad = k.map(b => b ^ 0x36);
  const opad = k.map(b => b ^ 0x5c);
  const innerHash = sha1([...ipad, ...msgBytes]);
  return sha1([...opad, ...Array.from(innerHash)]);
}

async function generateTotpCode(secretBase32, epochSeconds = Math.floor(Date.now() / 1000), stepSeconds = 30, digits = 6) {
  const counter = Math.floor(epochSeconds / stepSeconds);
  const counterBytes = new Uint8Array(8);
  const hiCounter = Math.floor(counter / 0x100000000);
  const loCounter = counter >>> 0;
  for (let i = 3; i >= 0; i--) counterBytes[3 - i] = (hiCounter >>> (i * 8)) & 0xff;
  for (let i = 3; i >= 0; i--) counterBytes[7 - i] = (loCounter >>> (i * 8)) & 0xff;

  const keyBytes = base32ToBytes(secretBase32);
  let hmac;
  try {
    if (window.crypto && window.crypto.subtle && typeof window.crypto.subtle.importKey === "function") {
      const cryptoKey = await window.crypto.subtle.importKey(
        "raw",
        keyBytes,
        { name: "HMAC", hash: { name: "SHA-1" } },
        false,
        ["sign"]
      );
      const sig = await window.crypto.subtle.sign("HMAC", cryptoKey, counterBytes.buffer);
      hmac = new Uint8Array(sig);
    } else {
      hmac = pureJsHmacSha1(keyBytes, counterBytes);
    }
  } catch (_) {
    hmac = pureJsHmacSha1(keyBytes, counterBytes);
  }
  const offset = hmac[hmac.length - 1] & 0x0f;
  const binary =
    ((hmac[offset] & 0x7f) << 24) |
    ((hmac[offset + 1] & 0xff) << 16) |
    ((hmac[offset + 2] & 0xff) << 8) |
    (hmac[offset + 3] & 0xff);

  const otp = binary % (10 ** digits);
  return String(otp).padStart(digits, "0");
}

async function verifyTotpCode(secretBase32, inputToken, windowSteps = 1) {
  const cleanToken = String(inputToken || "").replace(/\D/g, "");
  if (cleanToken.length !== 6) return false;
  const nowSec = Math.floor(Date.now() / 1000);
  for (let offsetStep = -windowSteps; offsetStep <= windowSteps; offsetStep++) {
    const expected = await generateTotpCode(secretBase32, nowSec + offsetStep * 30, 30, 6);
    if (expected === cleanToken) return true;
  }
  return false;
}

function getOrInitTotpSecret() {
  let secret = safeGetLocal(GATE_TOTP_SECRET_KEY);
  if (!secret) {
    secret = generateBase32Secret(20);
    safeSetLocal(GATE_TOTP_SECRET_KEY, secret);
  }
  return secret;
}

// Salted PBKDF2-HMAC-SHA256 password hashing (stronger client-side storage than unsalted hash)
const GATE_PASS_SALT_KEY = "TMC_GATE_PASS_SALT_V1";
const IDLE_TIMEOUT_MS = 15 * 60 * 1000; // 15 minutes auto-lock when idle
let lastActivityTime = Date.now();

function getOrCreatePassSalt() {
  let salt = safeGetLocal(GATE_PASS_SALT_KEY);
  if (!salt) {
    const arr = new Uint8Array(12);
    if (window.crypto && typeof window.crypto.getRandomValues === "function") {
      window.crypto.getRandomValues(arr);
    } else {
      for (let i = 0; i < 12; i++) arr[i] = Math.floor(Math.random() * 256);
    }
    salt = Array.from(arr).map(b => b.toString(16).padStart(2, "0")).join("");
    safeSetLocal(GATE_PASS_SALT_KEY, salt);
  }
  return salt;
}

async function hashPasswordWithSalt(passwordText) {
  const salt = getOrCreatePassSalt();
  const str = String(passwordText ?? "");
  try {
    if (window.crypto && window.crypto.subtle && typeof window.crypto.subtle.importKey === "function" && typeof window.crypto.subtle.deriveBits === "function") {
      const enc = new TextEncoder();
      const baseKey = await window.crypto.subtle.importKey("raw", enc.encode(str), { name: "PBKDF2" }, false, ["deriveBits"]);
      const bits = await window.crypto.subtle.deriveBits(
        { name: "PBKDF2", salt: enc.encode(salt), iterations: 100000, hash: "SHA-256" },
        baseKey,
        256
      );
      return "pbkdf2$" + Array.from(new Uint8Array(bits)).map(b => b.toString(16).padStart(2, "0")).join("");
    }
  } catch (_) {}
  // Fallback multi-round SHA-256 with salt when crypto.subtle is unavailable
  let cur = await sha256Hex(salt + ":" + str);
  for (let r = 0; r < 250; r++) {
    cur = await sha256Hex(cur + ":" + salt);
  }
  return "sha256r$" + cur;
}

async function ensureDefaultGatePasswordHash() {
  if (!safeGetLocal(GATE_PASS_HASH_KEY)) {
    const h = await hashPasswordWithSalt("1234");
    safeSetLocal(GATE_PASS_HASH_KEY, h);
  }
}

function buildOtpAuthUri(secret) {
  // Compact standard RFC 6238 URI -> produces crisp Version 4 (33x33) QR code with large modules for instant camera scan
  return `otpauth://totp/TMC:Admin?secret=${encodeURIComponent(secret)}&issuer=TMC`;
}

// Standard ISO/IEC 18004 QR Code Generator (Kazuhiko Arase MIT implementation — auto version & optimal mask)
const StandardQR = (function() {
  const PAD0 = 0xEC, PAD1 = 0x11;
  const MODE_8BIT_BYTE = 1 << 2;
  const ErrorCorrectLevel = { L: 1, M: 0, Q: 3, H: 2 };

  function QR8bitByte(data) {
    this.mode = MODE_8BIT_BYTE;
    this.parsedData = [];
    const utf8 = unescape(encodeURIComponent(String(data)));
    for (let i = 0; i < utf8.length; i++) {
      this.parsedData.push(utf8.charCodeAt(i));
    }
  }
  QR8bitByte.prototype.getLength = function() { return this.parsedData.length; };
  QR8bitByte.prototype.write = function(buffer) {
    for (let i = 0; i < this.parsedData.length; i++) {
      buffer.put(this.parsedData[i], 8);
    }
  };

  function QRBitBuffer() {
    this.buffer = [];
    this.length = 0;
  }
  QRBitBuffer.prototype.get = function(index) {
    const bufIndex = Math.floor(index / 8);
    return ((this.buffer[bufIndex] >>> (7 - index % 8)) & 1) === 1;
  };
  QRBitBuffer.prototype.put = function(num, length) {
    for (let i = 0; i < length; i++) {
      this.putBit(((num >>> (length - i - 1)) & 1) === 1);
    }
  };
  QRBitBuffer.prototype.putBit = function(bit) {
    const bufIndex = Math.floor(this.length / 8);
    if (this.buffer.length <= bufIndex) this.buffer.push(0);
    if (bit) this.buffer[bufIndex] |= (0x80 >>> (this.length % 8));
    this.length++;
  };

  const EXP_TABLE = new Array(256);
  const LOG_TABLE = new Array(256);
  for (let i = 0; i < 8; i++) EXP_TABLE[i] = 1 << i;
  for (let i = 8; i < 256; i++) {
    EXP_TABLE[i] = EXP_TABLE[i - 4] ^ EXP_TABLE[i - 5] ^ EXP_TABLE[i - 6] ^ EXP_TABLE[i - 8];
  }
  for (let i = 0; i < 255; i++) LOG_TABLE[EXP_TABLE[i]] = i;

  const QRMath = {
    glog: function(n) { if (n < 1) throw new Error("glog(" + n + ")"); return LOG_TABLE[n]; },
    gexp: function(n) { while (n < 0) n += 255; while (n >= 256) n -= 255; return EXP_TABLE[n]; }
  };

  function QRPolynomial(num, shift) {
    let offset = 0;
    while (offset < num.length && num[offset] === 0) offset++;
    this.num = new Array(num.length - offset + shift);
    for (let i = 0; i < num.length - offset; i++) this.num[i] = num[i + offset];
  }
  QRPolynomial.prototype.get = function(index) { return this.num[index]; };
  QRPolynomial.prototype.getLength = function() { return this.num.length; };
  QRPolynomial.prototype.multiply = function(e) {
    const num = new Array(this.getLength() + e.getLength() - 1);
    for (let i = 0; i < this.getLength(); i++) {
      for (let j = 0; j < e.getLength(); j++) {
        num[i + j] ^= QRMath.gexp(QRMath.glog(this.get(i)) + QRMath.glog(e.get(j)));
      }
    }
    return new QRPolynomial(num, 0);
  };
  QRPolynomial.prototype.mod = function(e) {
    if (this.getLength() - e.getLength() < 0) return this;
    const ratio = QRMath.glog(this.get(0)) - QRMath.glog(e.get(0));
    const num = new Array(this.getLength());
    for (let i = 0; i < this.getLength(); i++) num[i] = this.get(i);
    for (let i = 0; i < e.getLength(); i++) num[i] ^= QRMath.gexp(QRMath.glog(e.get(i)) + ratio);
    return new QRPolynomial(num, 0).mod(e);
  };

  const RS_BLOCK_TABLE = [
    [1, 26, 19], [1, 26, 16], [1, 26, 13], [1, 26, 9],
    [1, 44, 34], [1, 44, 28], [1, 44, 22], [1, 44, 16],
    [1, 70, 55], [1, 70, 44], [2, 35, 17], [2, 35, 13],
    [1, 100, 80], [2, 50, 32], [2, 50, 24], [4, 25, 9],
    [1, 134, 108], [2, 67, 43], [2, 33, 15, 2, 34, 16], [2, 33, 11, 2, 34, 12],
    [2, 86, 68], [4, 43, 27], [4, 43, 19], [4, 43, 15],
    [2, 98, 78], [4, 49, 31], [2, 32, 14, 4, 33, 15], [4, 39, 13, 1, 40, 14],
    [2, 121, 97], [2, 60, 38, 2, 61, 39], [4, 40, 18, 2, 41, 19], [4, 40, 14, 2, 41, 15],
    [2, 146, 116], [3, 58, 36, 2, 59, 37], [4, 36, 16, 4, 37, 17], [4, 36, 12, 4, 37, 13],
    [2, 86, 68, 2, 87, 69], [4, 69, 43, 1, 70, 44], [6, 43, 19, 2, 44, 20], [6, 43, 15, 2, 44, 16]
  ];

  function getRSBlocks(typeNumber, errorCorrectLevel) {
    let offset = 0;
    switch (errorCorrectLevel) {
      case ErrorCorrectLevel.L: offset = 0; break;
      case ErrorCorrectLevel.M: offset = 1; break;
      case ErrorCorrectLevel.Q: offset = 2; break;
      case ErrorCorrectLevel.H: offset = 3; break;
    }
    const rsBlock = RS_BLOCK_TABLE[(typeNumber - 1) * 4 + offset];
    const list = [];
    for (let i = 0; i < rsBlock.length / 3; i++) {
      const count = rsBlock[i * 3 + 0];
      const totalCount = rsBlock[i * 3 + 1];
      const dataCount = rsBlock[i * 3 + 2];
      for (let j = 0; j < count; j++) list.push({ totalCount, dataCount });
    }
    return list;
  }

  const PATTERN_POSITION_TABLE = [
    [], [6, 18], [6, 22], [6, 26], [6, 30], [6, 34],
    [6, 22, 38], [6, 24, 42], [6, 26, 46], [6, 28, 50]
  ];

  const G15 = (1 << 10) | (1 << 8) | (1 << 5) | (1 << 4) | (1 << 2) | (1 << 1) | (1 << 0);
  const G18 = (1 << 12) | (1 << 11) | (1 << 10) | (1 << 9) | (1 << 8) | (1 << 5) | (1 << 2) | (1 << 0);
  const G15_MASK = (1 << 14) | (1 << 12) | (1 << 10) | (1 << 4) | (1 << 1);

  function getBCHDigit(data) {
    let digit = 0;
    while (data !== 0) { digit++; data >>>= 1; }
    return digit;
  }
  function getBCHTypeInfo(data) {
    let d = data << 10;
    while (getBCHDigit(d) - getBCHDigit(G15) >= 0) {
      d ^= (G15 << (getBCHDigit(d) - getBCHDigit(G15)));
    }
    return ((data << 10) | d) ^ G15_MASK;
  }
  function getBCHTypeNumber(data) {
    let d = data << 12;
    while (getBCHDigit(d) - getBCHDigit(G18) >= 0) {
      d ^= (G18 << (getBCHDigit(d) - getBCHDigit(G18)));
    }
    return (data << 12) | d;
  }

  function getMask(maskPattern, i, j) {
    switch (maskPattern) {
      case 0: return (i + j) % 2 === 0;
      case 1: return i % 2 === 0;
      case 2: return j % 3 === 0;
      case 3: return (i + j) % 3 === 0;
      case 4: return (Math.floor(i / 2) + Math.floor(j / 3)) % 2 === 0;
      case 5: return (i * j) % 2 + (i * j) % 3 === 0;
      case 6: return ((i * j) % 2 + (i * j) % 3) % 2 === 0;
      case 7: return ((i * j) % 3 + (i + j) % 2) % 2 === 0;
      default: return false;
    }
  }

  function getErrorCorrectPolynomial(errorCorrectLength) {
    let a = new QRPolynomial([1], 0);
    for (let i = 0; i < errorCorrectLength; i++) {
      a = a.multiply(new QRPolynomial([1, QRMath.gexp(i)], 0));
    }
    return a;
  }

  function QRCodeModel(typeNumber, errorCorrectLevel) {
    this.typeNumber = typeNumber;
    this.errorCorrectLevel = errorCorrectLevel;
    this.modules = null;
    this.moduleCount = 0;
    this.dataCache = null;
    this.dataList = [];
  }
  QRCodeModel.prototype.addData = function(data) {
    this.dataList.push(new QR8bitByte(data));
    this.dataCache = null;
  };
  QRCodeModel.prototype.isDark = function(row, col) {
    return this.modules[row][col];
  };
  QRCodeModel.prototype.getModuleCount = function() {
    return this.moduleCount;
  };
  QRCodeModel.prototype.make = function() {
    if (this.typeNumber < 1) {
      let typeNumber = 1;
      for (typeNumber = 1; typeNumber <= 10; typeNumber++) {
        const rsBlocks = getRSBlocks(typeNumber, this.errorCorrectLevel);
        const buffer = new QRBitBuffer();
        let totalDataCount = 0;
        for (let i = 0; i < rsBlocks.length; i++) totalDataCount += rsBlocks[i].dataCount;
        for (let i = 0; i < this.dataList.length; i++) {
          const data = this.dataList[i];
          buffer.put(data.mode, 4);
          buffer.put(data.getLength(), typeNumber < 10 ? 8 : 16);
          data.write(buffer);
        }
        if (buffer.length <= totalDataCount * 8) break;
      }
      this.typeNumber = typeNumber;
    }
    this.makeImpl(false, this.getBestMaskPattern());
  };
  QRCodeModel.prototype.makeImpl = function(test, maskPattern) {
    this.moduleCount = this.typeNumber * 4 + 17;
    this.modules = new Array(this.moduleCount);
    for (let row = 0; row < this.moduleCount; row++) {
      this.modules[row] = new Array(this.moduleCount);
      for (let col = 0; col < this.moduleCount; col++) this.modules[row][col] = null;
    }
    this.setupPositionProbePattern(0, 0);
    this.setupPositionProbePattern(this.moduleCount - 7, 0);
    this.setupPositionProbePattern(0, this.moduleCount - 7);
    this.setupPositionAdjustPattern();
    this.setupTimingPattern();
    this.setupTypeInfo(test, maskPattern);
    if (this.typeNumber >= 7) this.setupTypeNumber(test);
    if (this.dataCache === null) {
      this.dataCache = QRCodeModel.createData(this.typeNumber, this.errorCorrectLevel, this.dataList);
    }
    this.mapData(this.dataCache, maskPattern);
  };
  QRCodeModel.prototype.setupPositionProbePattern = function(row, col) {
    for (let r = -1; r <= 7; r++) {
      if (row + r <= -1 || this.moduleCount <= row + r) continue;
      for (let c = -1; c <= 7; c++) {
        if (col + c <= -1 || this.moduleCount <= col + c) continue;
        if ((0 <= r && r <= 6 && (c === 0 || c === 6)) ||
            (0 <= c && c <= 6 && (r === 0 || r === 6)) ||
            (2 <= r && r <= 4 && 2 <= c && c <= 4)) {
          this.modules[row + r][col + c] = true;
        } else {
          this.modules[row + r][col + c] = false;
        }
      }
    }
  };
  QRCodeModel.prototype.getBestMaskPattern = function() {
    let minLostPoint = 0;
    let pattern = 0;
    for (let i = 0; i < 8; i++) {
      this.makeImpl(true, i);
      const lostPoint = getLostPoint(this);
      if (i === 0 || minLostPoint > lostPoint) {
        minLostPoint = lostPoint;
        pattern = i;
      }
    }
    return pattern;
  };
  QRCodeModel.prototype.setupTimingPattern = function() {
    for (let r = 8; r < this.moduleCount - 8; r++) {
      if (this.modules[r][6] !== null) continue;
      this.modules[r][6] = (r % 2 === 0);
    }
    for (let c = 8; c < this.moduleCount - 8; c++) {
      if (this.modules[6][c] !== null) continue;
      this.modules[6][c] = (c % 2 === 0);
    }
  };
  QRCodeModel.prototype.setupPositionAdjustPattern = function() {
    const pos = PATTERN_POSITION_TABLE[this.typeNumber - 1] || [];
    for (let i = 0; i < pos.length; i++) {
      for (let j = 0; j < pos.length; j++) {
        const row = pos[i], col = pos[j];
        if (this.modules[row][col] !== null) continue;
        for (let r = -2; r <= 2; r++) {
          for (let c = -2; c <= 2; c++) {
            this.modules[row + r][col + c] = (r === -2 || r === 2 || c === -2 || c === 2 || (r === 0 && c === 0));
          }
        }
      }
    }
  };
  QRCodeModel.prototype.setupTypeNumber = function(test) {
    const bits = getBCHTypeNumber(this.typeNumber);
    for (let i = 0; i < 18; i++) {
      const mod = (!test && ((bits >> i) & 1) === 1);
      this.modules[Math.floor(i / 3)][i % 3 + this.moduleCount - 8 - 3] = mod;
    }
    for (let i = 0; i < 18; i++) {
      const mod = (!test && ((bits >> i) & 1) === 1);
      this.modules[i % 3 + this.moduleCount - 8 - 3][Math.floor(i / 3)] = mod;
    }
  };
  QRCodeModel.prototype.setupTypeInfo = function(test, maskPattern) {
    const data = (this.errorCorrectLevel << 3) | maskPattern;
    const bits = getBCHTypeInfo(data);
    for (let i = 0; i < 15; i++) {
      const mod = (!test && ((bits >> i) & 1) === 1);
      if (i < 6) this.modules[i][8] = mod;
      else if (i < 8) this.modules[i + 1][8] = mod;
      else this.modules[this.moduleCount - 15 + i][8] = mod;
    }
    for (let i = 0; i < 15; i++) {
      const mod = (!test && ((bits >> i) & 1) === 1);
      if (i < 8) this.modules[8][this.moduleCount - i - 1] = mod;
      else if (i < 9) this.modules[8][15 - i - 1 + 1] = mod;
      else this.modules[8][15 - i - 1] = mod;
    }
    this.modules[this.moduleCount - 8][8] = (!test);
  };
  QRCodeModel.prototype.mapData = function(data, maskPattern) {
    let inc = -1;
    let row = this.moduleCount - 1;
    let bitIndex = 7;
    let byteIndex = 0;
    for (let col = this.moduleCount - 1; col > 0; col -= 2) {
      if (col === 6) col--;
      while (true) {
        for (let c = 0; c < 2; c++) {
          if (this.modules[row][col - c] === null) {
            let dark = false;
            if (byteIndex < data.length) dark = (((data[byteIndex] >>> bitIndex) & 1) === 1);
            if (getMask(maskPattern, row, col - c)) dark = !dark;
            this.modules[row][col - c] = dark;
            bitIndex--;
            if (bitIndex === -1) { byteIndex++; bitIndex = 7; }
          }
        }
        row += inc;
        if (row < 0 || this.moduleCount <= row) {
          row -= inc;
          inc = -inc;
          break;
        }
      }
    }
  };
  QRCodeModel.createData = function(typeNumber, errorCorrectLevel, dataList) {
    const rsBlocks = getRSBlocks(typeNumber, errorCorrectLevel);
    const buffer = new QRBitBuffer();
    for (let i = 0; i < dataList.length; i++) {
      const data = dataList[i];
      buffer.put(data.mode, 4);
      buffer.put(data.getLength(), typeNumber < 10 ? 8 : 16);
      data.write(buffer);
    }
    let totalDataCount = 0;
    for (let i = 0; i < rsBlocks.length; i++) totalDataCount += rsBlocks[i].dataCount;
    if (buffer.length + 4 <= totalDataCount * 8) buffer.put(0, 4);
    while (buffer.length % 8 !== 0) buffer.putBit(false);
    while (true) {
      if (buffer.length >= totalDataCount * 8) break;
      buffer.put(PAD0, 8);
      if (buffer.length >= totalDataCount * 8) break;
      buffer.put(PAD1, 8);
    }
    return QRCodeModel.createBytes(buffer, rsBlocks);
  };
  QRCodeModel.createBytes = function(buffer, rsBlocks) {
    let offset = 0;
    let maxDcCount = 0;
    let maxEcCount = 0;
    const dcdata = new Array(rsBlocks.length);
    const ecdata = new Array(rsBlocks.length);
    for (let r = 0; r < rsBlocks.length; r++) {
      const dcCount = rsBlocks[r].dataCount;
      const ecCount = rsBlocks[r].totalCount - dcCount;
      maxDcCount = Math.max(maxDcCount, dcCount);
      maxEcCount = Math.max(maxEcCount, ecCount);
      dcdata[r] = new Array(dcCount);
      for (let i = 0; i < dcdata[r].length; i++) dcdata[r][i] = 0xff & buffer.buffer[i + offset];
      offset += dcCount;
      const rsPoly = getErrorCorrectPolynomial(ecCount);
      const rawPoly = new QRPolynomial(dcdata[r], rsPoly.getLength() - 1);
      const modPoly = rawPoly.mod(rsPoly);
      ecdata[r] = new Array(rsPoly.getLength() - 1);
      for (let i = 0; i < ecdata[r].length; i++) {
        const modIndex = i + modPoly.getLength() - ecdata[r].length;
        ecdata[r][i] = (modIndex >= 0) ? modPoly.get(modIndex) : 0;
      }
    }
    let totalCodeCount = 0;
    for (let i = 0; i < rsBlocks.length; i++) totalCodeCount += rsBlocks[i].totalCount;
    const data = new Array(totalCodeCount);
    let index = 0;
    for (let i = 0; i < maxDcCount; i++) {
      for (let r = 0; r < rsBlocks.length; r++) {
        if (i < dcdata[r].length) data[index++] = dcdata[r][i];
      }
    }
    for (let i = 0; i < maxEcCount; i++) {
      for (let r = 0; r < rsBlocks.length; r++) {
        if (i < ecdata[r].length) data[index++] = ecdata[r][i];
      }
    }
    return data;
  };

  function getLostPoint(qrCode) {
    const moduleCount = qrCode.getModuleCount();
    let lostPoint = 0;
    for (let row = 0; row < moduleCount; row++) {
      for (let col = 0; col < moduleCount; col++) {
        let sameCount = 0;
        const dark = qrCode.isDark(row, col);
        for (let r = -1; r <= 1; r++) {
          if (row + r < 0 || moduleCount <= row + r) continue;
          for (let c = -1; c <= 1; c++) {
            if (col + c < 0 || moduleCount <= col + c) continue;
            if (r === 0 && c === 0) continue;
            if (dark === qrCode.isDark(row + r, col + c)) sameCount++;
          }
        }
        if (sameCount > 5) lostPoint += (3 + sameCount - 5);
      }
    }
    for (let row = 0; row < moduleCount - 1; row++) {
      for (let col = 0; col < moduleCount - 1; col++) {
        let count = 0;
        if (qrCode.isDark(row, col)) count++;
        if (qrCode.isDark(row + 1, col)) count++;
        if (qrCode.isDark(row, col + 1)) count++;
        if (qrCode.isDark(row + 1, col + 1)) count++;
        if (count === 0 || count === 4) lostPoint += 3;
      }
    }
    for (let row = 0; row < moduleCount; row++) {
      for (let col = 0; col < moduleCount - 6; col++) {
        if (qrCode.isDark(row, col) && !qrCode.isDark(row, col + 1) && qrCode.isDark(row, col + 2) &&
            qrCode.isDark(row, col + 3) && qrCode.isDark(row, col + 4) && !qrCode.isDark(row, col + 5) && qrCode.isDark(row, col + 6)) {
          lostPoint += 40;
        }
      }
    }
    for (let col = 0; col < moduleCount; col++) {
      for (let row = 0; row < moduleCount - 6; row++) {
        if (qrCode.isDark(row, col) && !qrCode.isDark(row + 1, col) && qrCode.isDark(row + 2, col) &&
            qrCode.isDark(row + 3, col) && qrCode.isDark(row + 4, col) && !qrCode.isDark(row + 5, col) && qrCode.isDark(row + 6, col)) {
          lostPoint += 40;
        }
      }
    }
    let darkCount = 0;
    for (let col = 0; col < moduleCount; col++) {
      for (let row = 0; row < moduleCount; row++) {
        if (qrCode.isDark(row, col)) darkCount++;
      }
    }
    const ratio = Math.abs(100 * darkCount / moduleCount / moduleCount - 50) / 5;
    lostPoint += ratio * 10;
    return lostPoint;
  }

  return {
    createMatrix: function(text) {
      const qr = new QRCodeModel(-1, ErrorCorrectLevel.M);
      qr.addData(text);
      qr.make();
      const count = qr.getModuleCount();
      const mat = [];
      for (let r = 0; r < count; r++) {
        const rowArr = [];
        for (let c = 0; c < count; c++) rowArr.push(qr.isDark(r, c) ? 1 : 0);
        mat.push(rowArr);
      }
      return mat;
    }
  };
})();

function drawTotpQrMatrix(canvasEl, uriText) {
  if (!canvasEl) return;
  const ctx = canvasEl.getContext("2d");
  const matrix = StandardQR.createMatrix(uriText);
  const count = matrix.length;
  const quietZone = 4; // Standard 4-module white border required by iPhone & Authenticator scanners
  const totalCells = count + quietZone * 2;
  const scale = Math.max(4, Math.floor(220 / totalCells));
  const pixelSize = totalCells * scale;

  canvasEl.width = pixelSize;
  canvasEl.height = pixelSize;

  ctx.fillStyle = "#ffffff";
  ctx.fillRect(0, 0, pixelSize, pixelSize);

  ctx.fillStyle = "#000000";
  for (let r = 0; r < count; r++) {
    for (let c = 0; c < count; c++) {
      if (matrix[r][c] === 1) {
        ctx.fillRect((quietZone + c) * scale, (quietZone + r) * scale, scale, scale);
      }
    }
  }
}

function isGateAuthenticated() {
  return safeGetSession(GATE_SESSION_KEY) === "true";
}

let step1PasswordVerified = false;
let firstTimeEnrollSecret = "";

function sync2faStatusUI() {
  const enabled = is2faEnabled();
  const admin2faStatus = document.getElementById("admin2faStatusText");
  const disable2faBtn = document.getElementById("disable2faBtn");

  if (admin2faStatus) {
    admin2faStatus.textContent = enabled
      ? "สถานะ: เปิดใช้งานแล้ว (บังคับกรอกรหัส 6 หลักจาก iPhone / Authenticator ทุกครั้งหลังใส่รหัสผ่าน)"
      : "สถานะ: ยังไม่ได้เปิดใช้งาน";
  }
  if (disable2faBtn) {
    disable2faBtn.style.display = enabled ? "inline-block" : "none";
  }
}

function showLoginStep(stepNumber) {
  const step1Form = document.getElementById("gateStep1Form");
  const step2VerifyForm = document.getElementById("gateStep2VerifyForm");
  const step2EnrollForm = document.getElementById("gateStep2EnrollForm");
  const pill1 = document.getElementById("loginStepPill1");
  const pill2 = document.getElementById("loginStepPill2");
  const heading = document.getElementById("loginGateHeading");
  const subheading = document.getElementById("loginGateSubheading");

  if (!step1Form || !step2VerifyForm || !step2EnrollForm) return;

  if (stepNumber === 1) {
    step1PasswordVerified = false;
    step1Form.style.display = "flex";
    step2VerifyForm.style.display = "none";
    step2EnrollForm.style.display = "none";
    if (pill1) { pill1.className = "step-pill active"; }
    if (pill2) { pill2.className = "step-pill"; }
    if (heading) heading.textContent = "Sign in to Dashboard";
    if (subheading) subheading.textContent = "ขั้นตอนที่ 1: กรอกรหัสผ่านหลักเพื่อดำเนินการต่อ";
    const err1 = document.getElementById("gateStep1Error");
    if (err1) err1.style.display = "none";
    const qrDrawer = document.getElementById("step2QrDrawer");
    if (qrDrawer) qrDrawer.style.display = "none";
    const passInp = document.getElementById("gatePasswordInput");
    if (passInp) {
      passInp.value = "";
      setTimeout(() => passInp.focus(), 60);
    }
  } else {
    step1Form.style.display = "none";
    if (pill1) { pill1.className = "step-pill done"; }
    if (pill2) { pill2.className = "step-pill active"; }
    if (heading) heading.textContent = "2-Step Verification";

    if (is2faEnabled()) {
      step2VerifyForm.style.display = "flex";
      step2EnrollForm.style.display = "none";
      if (subheading) subheading.textContent = "ขั้นตอนที่ 2: กรอกรหัส OTP 6 หลักจาก iPhone / Authenticator";
      const err2 = document.getElementById("gateStep2Error");
      if (err2) err2.style.display = "none";
      const otpInp = document.getElementById("gateOtpInput");
      if (otpInp) {
        otpInp.value = "";
        setTimeout(() => otpInp.focus(), 60);
      }
    } else {
      // First-time enrollment right after Step 1 password succeeds
      step2VerifyForm.style.display = "none";
      step2EnrollForm.style.display = "flex";
      if (subheading) subheading.textContent = "ขั้นตอนที่ 2: ผูกแอป Passwords บน iPhone / Authenticator";
      if (!firstTimeEnrollSecret) {
        firstTimeEnrollSecret = generateBase32Secret(16);
      }
      setSecretDisplayValue("firstEnrollSecretDisplay", firstTimeEnrollSecret, false);
      const revFirstBtn = document.getElementById("revealFirstEnrollKeyBtn");
      if (revFirstBtn) revFirstBtn.textContent = "แสดง Key";
      drawTotpQrMatrix(document.getElementById("firstEnrollQrCanvas"), buildOtpAuthUri(firstTimeEnrollSecret));
      const errEnroll = document.getElementById("gateEnrollError");
      if (errEnroll) errEnroll.style.display = "none";
      const enrollInp = document.getElementById("firstEnrollOtpInput");
      if (enrollInp) {
        enrollInp.value = "";
        setTimeout(() => enrollInp.focus(), 60);
      }
    }
  }
}

function setLoginGateVisible(visible) {
  const gateEl = document.getElementById("loginGate");
  if (!gateEl) return;
  sync2faStatusUI();
  gateEl.style.display = visible ? "flex" : "none";
  if (visible) {
    showLoginStep(1);
  }
}

// Universal Dynamic Google Sheets Dashboard Engine (รองรับทุก Sheet, ทุก Tab, ทุกจำนวนคอลัมน์และแถวอัตโนมัติ)
let sheetHeaders = [];
let visibleTableHeaders = [];

function loadVisibleHeaders(sheetKey, allHeaders) {
  try {
    const raw = safeGetLocal(`GSHEET_VISIBLE_COLS_${sheetKey}`);
    if (raw) {
      const parsed = JSON.parse(raw);
      if (Array.isArray(parsed)) {
        const valid = parsed.filter(h => allHeaders.includes(h));
        if (valid.length > 0) return valid;
      }
    }
  } catch (_) {}
  return [...allHeaders];
}

function saveVisibleHeaders(sheetKey, selectedCols) {
  try {
    safeSetLocal(`GSHEET_VISIBLE_COLS_${sheetKey}`, JSON.stringify(selectedCols));
  } catch (_) {}
}
let rowsData = [];
let availableTabs = [];
let activeTabName = safeGetLocal("GSHEET_TAB_NAME") || "";
let connectionSource = safeGetLocal("GSHEET_SOURCE_INPUT") || "";
let connectionMode = "none"; // "apps_script" | "public_gviz" | "none"
let isConnected = false;
let isSavingToSheet = false;

let selectedGroupCol = safeGetLocal("GSHEET_GROUP_COL") || "";
let activeCardFilter = null;
let customCardConfigs = []; // [{ col: string, val: string }, ...] for Card 2, Card 3, Card 4

function loadCustomCardConfigs(sheetKey) {
  try {
    const raw = safeGetLocal(`GSHEET_CARD_CONFIGS_V2_${sheetKey}`);
    if (raw) {
      const parsed = JSON.parse(raw);
      if (Array.isArray(parsed)) return parsed;
    }
  } catch (_) {}
  return [];
}

function saveCustomCardConfigs(sheetKey, configs) {
  try {
    safeSetLocal(`GSHEET_CARD_CONFIGS_V2_${sheetKey}`, JSON.stringify(configs));
  } catch (_) {}
}

function getColumnValueCounts(colName, scopedRows) {
  const counts = {};
  scopedRows.forEach(r => {
    const val = String(r[colName] ?? "").trim() || "(ว่าง)";
    counts[val] = (counts[val] || 0) + 1;
  });
  const sortedGroups = Object.entries(counts).sort((a, b) => b[1] - a[1]);
  const nonEmptyGroups = sortedGroups.filter(([val]) => val !== "(ว่าง)");
  const orderedValues = [...nonEmptyGroups.map(([v]) => v), ...sortedGroups.filter(([val]) => val === "(ว่าง)").map(([v]) => v)];
  return { counts, sortedGroups, orderedValues };
}
let selectedSecondaryCol = "";
let activeNavView = "overview"; // "overview" | "jobs" | "analytics"
let sumPrimaryCol = "";
let sumSecondaryCol = "";
let sumDateCol = "";
let selectedSecondaryValue = "ALL";
let currentSearch = "";
let sortState = { column: "", direction: "asc" };
const ROWS_PER_PAGE = 20;
let currentPage = 1;
let rowCutoffLimit = Number(safeGetLocal("GSHEET_ROW_CUTOFF")) || 0; // 0 = แสดงทั้งหมด, >0 = แสดงถึงแถวที่ระบุ และเลื่อนตามอัตโนมัติเมื่อมีการกรอกข้อมูลเพิ่มในฟอร์มถัดไป
let rowCutoffBaselineFilled = Number(safeGetLocal("GSHEET_ROW_CUTOFF_BASELINE_FILLED")) || 0;
let hideTemplateBlanks = safeGetLocal("GSHEET_HIDE_TEMPLATE_BLANKS") !== "false";

// ตรวจสอบว่าเป็น "แถวที่กรอกข้อมูลจริงแล้ว" หรือเป็นแค่ "แถวฟอร์มที่รันเลข Job / ใส่ขีด '-' รอไว้เฉยๆ"
function isSubstantiveDataRow(row) {
  if (!row || sheetHeaders.length === 0) return false;
  // นับจำนวนคอลัมน์ที่ไม่ใช่คอลัมน์แรก (หรือคอลัมน์ที่ 2 ขึ้นไป เช่น Date, Customer, Equipment) ที่มีค่าจริง (ไม่ใช่ว่าง และไม่ใช่แค่ '-')
  let filledDetailCols = 0;
  for (let i = 1; i < sheetHeaders.length; i++) {
    const val = String(row[sheetHeaders[i]] ?? "").trim();
    if (val !== "" && val !== "-" && val !== "--") {
      filledDetailCols++;
    }
  }
  // ถ้ามีรายละเอียดอย่างน้อย 1 ช่อง (เช่น วันที่ หรือ ชื่อลูกค้า หรือ เครื่องมือ) ถือว่าเป็นข้อมูลจริง
  return filledDetailCols >= 1;
}

// หาตำแหน่งใน rowsData ของแถวที่มีหมายเลข _rowIndex ตรงกับ cutoff หรือใกล้เคียงที่สุด
function getEffectiveCutoff() {
  if (rowCutoffLimit <= 0) return 0;

  // นับจำนวนแถวที่มีข้อมูลจริงทั้งหมดในตอนนี้ เทียบกับตอนที่ผู้ใช้ตั้งค่าครั้งแรก
  const currentSubstantiveCount = rowsData.filter(isSubstantiveDataRow).length;
  const newlyFilledDelta = (rowCutoffBaselineFilled > 0 && currentSubstantiveCount > rowCutoffBaselineFilled)
    ? (currentSubstantiveCount - rowCutoffBaselineFilled)
    : 0;

  return rowCutoffLimit + newlyFilledDelta;
}

function getScopedRows() {
  const effectiveSheetRow = getEffectiveCutoff();
  let scoped = rowsData;

  if (effectiveSheetRow > 0) {
    // กรองเอาเฉพาะแถวที่มีเลขบรรทัดใน Google Sheet (_rowIndex) <= effectiveSheetRow (เช่น Row 1 ถึง 5687 และเมื่อกรอก 5688 จะขยับเป็น <= 5688 อัตโนมัติ)
    scoped = scoped.filter(r => (r._rowIndex || 0) <= effectiveSheetRow);
  }

  if (hideTemplateBlanks) {
    scoped = scoped.filter(isSubstantiveDataRow);
  }

  return scoped;
}

function syncRowLimitUI() {
  const box = document.getElementById("rowLimitControlBox");
  const inp = document.getElementById("rowLimitInput");
  const clearBtn = document.getElementById("clearRowLimitBtn");
  const chk = document.getElementById("hideTemplateBlanksCheck");
  if (!box || !inp || !clearBtn) return;

  const effectiveLimit = getEffectiveCutoff();
  box.style.display = isConnected && rowsData.length > 0 ? "inline-flex" : "none";
  if (document.activeElement !== inp) {
    inp.value = effectiveLimit > 0 ? String(effectiveLimit) : "";
  }
  if (chk) chk.checked = hideTemplateBlanks;

  if (effectiveLimit > 0) {
    box.classList.add("active");
    clearBtn.style.display = "inline-block";
  } else {
    box.classList.remove("active");
    clearBtn.style.display = "none";
  }
}

let editingRowObj = null;
let pendingDeleteRowObj = null;
let pollTimer = null;

let isAdminMode = safeGetSession("CALIB_IS_ADMIN") === "true";
let isDirectoryExpanded = safeGetLocal("CALIB_DIR_EXPANDED") !== "false";
const DEFAULT_ADMIN_PIN = "1234";

function getStoredAdminPin() {
  return safeGetLocal("CALIB_ADMIN_PIN") || DEFAULT_ADMIN_PIN;
}

function escapeHtml(value) {
  return String(value ?? "")
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

function showToast(message) {
  const container = document.getElementById("toastContainer");
  if (!container) return;
  const toast = document.createElement("div");
  toast.className = "toast";
  toast.textContent = message;
  container.appendChild(toast);
  setTimeout(() => toast.remove(), 3400);
}

// แปลง URL ที่ผู้ใช้กรอกให้รองรับทั้ง Apps Script Web App URL และลิงก์ Google Sheet โดยตรง
function parseConnectionTarget(rawInput, tabOverride = "") {
  const trimmed = String(rawInput || "").trim();
  if (!trimmed) return { mode: "none" };

  // กรณีที่ 1: Google Apps Script Web App URL
  if (trimmed.startsWith("https://script.google.com/")) {
    return {
      mode: "apps_script",
      execUrl: trimmed,
      tabName: tabOverride.trim()
    };
  }

  // กรณีที่ 2: ลิงก์ Google Sheets โดยตรง (https://docs.google.com/spreadsheets/d/{ID}/...)
  const sheetIdMatch = trimmed.match(/\/spreadsheets\/d\/([a-zA-Z0-9-_]+)/);
  if (sheetIdMatch) {
    const spreadsheetId = sheetIdMatch[1];
    const gidMatch = trimmed.match(/[#&?]gid=([0-9]+)/);
    return {
      mode: "public_gviz",
      spreadsheetId,
      gid: gidMatch ? gidMatch[1] : "",
      tabName: tabOverride.trim()
    };
  }

  return { mode: "invalid" };
}

function applyRoleUI() {
  const body = document.body;
  const toggleBtn = document.getElementById("adminToggleBtn");
  const roleLabel = document.getElementById("roleLabel");
  const dirBadge = document.getElementById("directoryModeBadge");

  if (isAdminMode) {
    body.classList.add("is-admin");
    if (toggleBtn) {
      toggleBtn.classList.remove("viewer");
      toggleBtn.classList.add("admin");
    }
    if (roleLabel) roleLabel.textContent = "Admin Mode";
    if (dirBadge) {
      dirBadge.textContent = connectionMode === "apps_script" ? "Admin Editable" : "Admin (Read-Only Link)";
      dirBadge.classList.remove("viewer");
      dirBadge.classList.add("admin");
    }
  } else {
    body.classList.remove("is-admin");
    if (toggleBtn) {
      toggleBtn.classList.remove("admin");
      toggleBtn.classList.add("viewer");
    }
    if (roleLabel) roleLabel.textContent = "Viewer Mode";
    if (dirBadge) {
      dirBadge.textContent = "View Only";
      dirBadge.classList.remove("admin");
      dirBadge.classList.add("viewer");
    }
  }
}

function applyDirectoryCollapseUI() {
  const dirBody = document.getElementById("directoryBody");
  const toggleBtn = document.getElementById("toggleDirectoryBtn");
  const toggleText = document.getElementById("toggleDirectoryText");
  if (!dirBody || !toggleBtn || !toggleText) return;

  if (isDirectoryExpanded) {
    dirBody.classList.remove("collapsed");
    toggleBtn.classList.remove("collapsed");
    toggleBtn.setAttribute("aria-expanded", "true");
    toggleText.textContent = "Hide Directory";
  } else {
    dirBody.classList.add("collapsed");
    toggleBtn.classList.add("collapsed");
    toggleBtn.setAttribute("aria-expanded", "false");
    toggleText.textContent = "Show Directory";
  }
}

function updateConnectionState(stateText, statusType = "offline") {
  const syncTextEl = document.getElementById("syncText");
  const syncDotEl = document.getElementById("syncDot");

  if (syncTextEl) syncTextEl.textContent = stateText;

  if (syncDotEl) {
    syncDotEl.className = "status-dot";
    if (statusType === "offline") syncDotEl.classList.add("offline");
    if (statusType === "syncing") syncDotEl.classList.add("syncing");
  }

  const hasSource = Boolean(connectionSource);
  const canWrite = Boolean(isConnected && connectionMode === "apps_script");

  document.getElementById("refreshNowBtn").disabled = !hasSource;
  document.getElementById("overviewSyncBtn").disabled = !hasSource;
  document.getElementById("openAddJobBtn").disabled = !canWrite;
  document.getElementById("overviewAddBtn").disabled = !canWrite;
  document.getElementById("overviewExportBtn").disabled = !isConnected || rowsData.length === 0;
  document.getElementById("tableExportCsvBtn").disabled = !isConnected || rowsData.length === 0;
  const sumExpBtn = document.getElementById("exportSummaryCsvBtn");
  if (sumExpBtn) sumExpBtn.disabled = !isConnected || rowsData.length === 0;
  document.getElementById("selectTableColsBtn").disabled = !isConnected || sheetHeaders.length === 0;
  document.getElementById("navConnectLabel").textContent = isConnected ? "Sheet Connected" : "Connect Sheet";
  document.getElementById("throughputBadge").textContent = isConnected
    ? (connectionMode === "apps_script" ? "2-Way Sync" : "Live View")
    : "Offline";

  applyRoleUI();
}

// วิเคราะห์คอลัมน์อัตโนมัติเพื่อหาคอลัมน์หมวดหมู่ (เช่น Status, ประเภท, แผนก) มาทำ KPI Cards
function detectBestGroupingColumns() {
  if (sheetHeaders.length === 0 || rowsData.length === 0) {
    selectedGroupCol = "";
    selectedSecondaryCol = "";
    return;
  }

  // หาคอลัมน์ที่มีค่าซ้ำกันเป็นหมวดหมู่ (จำนวนค่าที่ไม่ซ้ำอยู่ระหว่าง 2 ถึง 12 ค่า)
  const candidates = sheetHeaders.map(col => {
    const vals = rowsData.map(r => String(r[col] ?? "").trim()).filter(v => v !== "");
    const unique = new Set(vals);
    return { col, uniqueCount: unique.size, nonEmpty: vals.length };
  }).filter(item => item.nonEmpty > 0 && item.uniqueCount >= 2 && item.uniqueCount <= 15);

  // ให้ความสำคัญกับคอลัมน์ที่มีคำว่า status, สถานะ, type, category, group, แผนก, ช่าง, technician
  const priorityRegex = /(status|สถานะ|type|category|group|department|แผนก|ช่าง|tech|state|ระดับ|priority)/i;
  candidates.sort((a, b) => {
    const aPrio = priorityRegex.test(a.col) ? 0 : 1;
    const bPrio = priorityRegex.test(b.col) ? 0 : 1;
    if (aPrio !== bPrio) return aPrio - bPrio;
    return a.uniqueCount - b.uniqueCount;
  });

  if (!selectedGroupCol || !sheetHeaders.includes(selectedGroupCol)) {
    selectedGroupCol = candidates.length > 0 ? candidates[0].col : (sheetHeaders[sheetHeaders.length - 1] || sheetHeaders[0]);
  }
  customCardConfigs = loadCustomCardConfigs(activeTabName || "default");

  const secondaryCand = candidates.find(c => c.col !== selectedGroupCol);
  selectedSecondaryCol = secondaryCand ? secondaryCand.col : "";
}

function renderDotRuler(elementId, ratio) {
  const el = document.getElementById(elementId);
  if (!el) return;
  const totalDots = 17;
  const activeIdx = Math.min(totalDots - 1, Math.max(0, Math.round(ratio * (totalDots - 1))));
  let html = "";
  for (let i = 0; i < totalDots; i++) {
    html += i === activeIdx ? `<span class="r-tick"></span>` : `<span class="r-dot"></span>`;
  }
  el.innerHTML = html;
}

function renderSlaEqualizer(pct) {
  const el = document.getElementById("slaEqualizerScale");
  if (!el) return;
  const totalBars = 36;
  const filledBars = Math.round((Math.min(100, Math.max(0, pct)) / 100) * totalBars);
  let html = "";
  for (let i = 0; i < totalBars; i++) {
    const heightClass = i % 6 === 0 ? "tall" : (i % 3 === 0 ? "med" : "short");
    const filledClass = i < filledBars ? "filled" : "";
    html += `<span class="eq-bar ${heightClass} ${filledClass}"></span>`;
  }
  el.innerHTML = html;
}

function renderThroughputWidget(filteredCount, totalRows) {
  const donutEl = document.getElementById("statusDonutContainer");
  const matchPct = totalRows > 0 ? Math.round((filteredCount / totalRows) * 100) : 0;

  if (donutEl) {
    const r = 36;
    const c = 2 * Math.PI * r;
    const offset = c - (matchPct / 100) * c;
    donutEl.innerHTML = `
      <svg viewBox="0 0 96 96" width="96" height="96">
        <circle cx="48" cy="48" r="${r}" fill="none" stroke="#e2ebf3" stroke-width="11"/>
        <circle cx="48" cy="48" r="${r}" fill="none" stroke="#0ea5e9" stroke-width="11"
          stroke-dasharray="${c}" stroke-dashoffset="${offset}" stroke-linecap="round"
          transform="rotate(-90 48 48)"/>
      </svg>
    `;
  }

  // คำนวณอัตราความสมบูรณ์ของข้อมูลในทุกช่อง (Cell Fill Rate)
  let totalCells = totalRows * sheetHeaders.length;
  let filledCells = 0;
  getScopedRows().forEach(row => {
    sheetHeaders.forEach(h => {
      if (String(row[h] ?? "").trim() !== "") filledCells++;
    });
  });
  const fillRate = totalCells > 0 ? Math.round((filledCells / totalCells) * 100) : 0;

  document.getElementById("donutActiveCount").textContent = filteredCount;
  document.getElementById("donutOnTimeRate").textContent = `${fillRate}%`;

  // วาดกราฟแท่งแสดงอัตราข้อมูลครบถ้วนของแต่ละคอลัมน์ (สูงสุด 7 คอลัมน์แรก)
  const barsEl = document.getElementById("weeklyBarChart");
  if (barsEl) {
    if (sheetHeaders.length === 0 || totalRows === 0) {
      barsEl.innerHTML = ["C1", "C2", "C3", "C4", "C5", "C6", "C7"].map(lbl => `
        <div class="w-bar-col">
          <div class="w-bar-pill" style="height: 18px;"></div>
          <span class="w-bar-day">${lbl}</span>
        </div>
      `).join("");
    } else {
      const colsToShow = sheetHeaders.slice(0, 7);
      barsEl.innerHTML = colsToShow.map((col, idx) => {
        const nonEmpty = getScopedRows().filter(r => String(r[col] ?? "").trim() !== "").length;
        const ratio = nonEmpty / totalRows;
        const h = Math.max(18, Math.round(ratio * 64));
        const cls = idx === 0 ? "today" : (nonEmpty > 0 ? "has-val" : "");
        const shortName = col.length > 5 ? col.slice(0, 4) + "." : col;
        return `
          <div class="w-bar-col" title="${escapeHtml(col)}: ${nonEmpty}/${totalRows} rows filled">
            <div class="w-bar-pill ${cls}" style="height: ${h}px;"></div>
            <span class="w-bar-day">${escapeHtml(shortName)}</span>
          </div>
        `;
      }).join("");
    }
  }
}

function renderLatestRecordsPreview() {
  const listEl = document.getElementById("priorityQueueList");
  if (!listEl) return;

  const scoped = getScopedRows();
  document.getElementById("planRatioLabel").textContent = `${Math.min(4, scoped.length)}/${scoped.length}`;

  if (!isConnected || scoped.length === 0 || sheetHeaders.length === 0) {
    listEl.innerHTML = `
      <div class="plan-row-pill">
        <div class="plan-left">
          <span class="check-circle"></span>
          <span class="plan-title" style="color: var(--ink-muted);">${!isConnected ? "Connect any Google Sheet to preview rows" : "No data rows found in this sheet"}</span>
        </div>
        <span class="plan-time">--</span>
      </div>
    `;
    return;
  }

  const col1 = sheetHeaders[0];
  const col2 = sheetHeaders[1] || sheetHeaders[0];
  const colLast = sheetHeaders[sheetHeaders.length - 1];

  const previewRows = [...scoped].reverse().slice(0, 4);
  listEl.innerHTML = previewRows.map(row => {
    const primaryText = col1 !== col2
      ? `${row[col1] || "-"} — ${row[col2] || "-"}`
      : `${row[col1] || "-"}`;
    const badgeVal = String(row[colLast] || "").trim();
    return `
      <div class="plan-row-pill done-tint">
        <div class="plan-left">
          <span class="check-circle">
            <svg width="11" height="11" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3"><polyline points="20 6 9 17 4 12"/></svg>
          </span>
          <span class="plan-title">${escapeHtml(primaryText)}</span>
        </div>
        <span class="plan-time">${escapeHtml(badgeVal)}</span>
      </div>
    `;
  }).join("");
}

function renderAnalytics() {
  const scopedRows = getScopedRows();
  const totalRows = scopedRows.length;
  const totalCols = sheetHeaders.length;
  const filtered = getFilteredAndSortedRows();
  syncRowLimitUI();

  // Top Right Metrics
  document.getElementById("heroTopRows").textContent = totalRows;
  document.getElementById("heroTopCols").textContent = totalCols;
  document.getElementById("heroTopFiltered").textContent = filtered.length;
  document.getElementById("seeAllCount").textContent = totalRows;

  // Group-By Column Selector & Customize Button
  const groupSelect = document.getElementById("groupByColSelect");
  const customizeBtn = document.getElementById("customizeCardsBtn");
  if (sheetHeaders.length > 0 && isConnected) {
    groupSelect.style.display = "inline-block";
    customizeBtn.style.display = "inline-block";
    groupSelect.innerHTML = sheetHeaders.map(h =>
      `<option value="${escapeHtml(h)}" ${h === selectedGroupCol ? "selected" : ""}>Column: ${escapeHtml(h)}</option>`
    ).join("");
  } else {
    groupSelect.style.display = "none";
    customizeBtn.style.display = "none";
  }

  // Dynamic 4-Column Sub-Metrics Grid
  const metricsGrid = document.getElementById("dynamicSubMetricsGrid");
  const colFilterSelect = document.getElementById("dynamicColFilterSelect");
  metricsGrid.innerHTML = "";

  if (!isConnected || totalCols === 0) {
    colFilterSelect.style.display = "none";
    const placeholders = [
      { label: "Total Rows", tag: "Ready", val: "0", unit: "rows", desc: "Connect sheet" },
      { label: "Columns", tag: "Auto", val: "0", unit: "cols", desc: "Dynamic schema" },
      { label: "Filtered", tag: "Live", val: "0", unit: "rows", desc: "Active view" },
      { label: "Tabs", tag: "Sync", val: "0", unit: "tabs", desc: "Multi-sheet" }
    ];
    metricsGrid.innerHTML = placeholders.map((p, idx) => `
      <div class="sub-metric-item ${idx === 0 ? "active" : ""}">
        <div class="sub-top"><span>${p.label}</span><span class="status-tag tag-sky">${p.tag}</span></div>
        <div class="sub-val-row"><strong>${p.val}</strong><small>${p.unit}</small></div>
        <div class="sub-desc">${p.desc}</div>
        <div class="dot-ruler" id="rulerPlaceholder_${idx}"></div>
      </div>
    `).join("");
    [0.2, 0.2, 0.2, 0.2].forEach((r, idx) => renderDotRuler(`rulerPlaceholder_${idx}`, r));
  } else {
    // อัปเดต Dropdown กรองในแถบเครื่องมือตารางตามคอลัมน์หลัก (หรือคอลัมน์ของการ์ดที่ถูกคลิกเลือก)
    const toolbarFilterCol = (activeCardFilter && sheetHeaders.includes(activeCardFilter.col))
      ? activeCardFilter.col
      : selectedGroupCol;
    const { sortedGroups: toolbarGroups } = getColumnValueCounts(toolbarFilterCol, scopedRows);

    colFilterSelect.style.display = "inline-block";
    colFilterSelect.innerHTML = `<option value="ALL">ทุกค่าใน ${escapeHtml(toolbarFilterCol)} (All)</option>` +
      toolbarGroups.map(([val, cnt]) => {
        const isSel = activeCardFilter && activeCardFilter.col === toolbarFilterCol && activeCardFilter.val === val;
        return `<option value="${escapeHtml(val)}" ${isSel ? "selected" : ""}>${escapeHtml(val)} (${cnt})</option>`;
      }).join("");

    // เตรียมค่าเริ่มต้นสำหรับการ์ดช่องที่ 2, 3, 4 (รองรับคอลัมน์แยกอิสระในแต่ละการ์ด!)
    const defaultColInfo = getColumnValueCounts(selectedGroupCol, scopedRows);
    const resolvedConfigs = [0, 1, 2].map(slotIdx => {
      const saved = customCardConfigs[slotIdx];
      const col = (saved && saved.col && sheetHeaders.includes(saved.col)) ? saved.col : selectedGroupCol;
      const colInfo = getColumnValueCounts(col, scopedRows);
      let val = (saved && saved.val && colInfo.orderedValues.includes(saved.val)) ? saved.val : "";
      if (!val) {
        // เลือกค่าอันดับต้นๆ ที่ไม่ซ้ำกับช่องก่อนหน้าในคอลัมน์เดียวกัน
        val = colInfo.orderedValues[slotIdx] || colInfo.orderedValues[0] || "(ว่าง)";
      }
      return { col, val, counts: colInfo.counts, orderedValues: colInfo.orderedValues };
    });

    const isAllActive = !activeCardFilter;
    const cardsData = [
      {
        slotIdx: -1,
        col: "",
        val: "ALL",
        title: "Total Records",
        tag: "All",
        tagClass: "tag-sky",
        count: totalRows,
        desc: `${totalCols} columns detected`,
        isActive: isAllActive
      }
    ];

    const tagStyles = ["tag-blue", "tag-mint", "tag-coral"];
    resolvedConfigs.forEach((cfg, i) => {
      const cnt = cfg.counts[cfg.val] || 0;
      const pct = totalRows > 0 ? Math.round((cnt / totalRows) * 100) : 0;
      const isCardActive = Boolean(activeCardFilter && activeCardFilter.col === cfg.col && activeCardFilter.val === cfg.val);
      cardsData.push({
        slotIdx: i,
        col: cfg.col,
        val: cfg.val,
        orderedValues: cfg.orderedValues,
        title: cfg.val,
        tag: `${pct}%`,
        tagClass: tagStyles[i % tagStyles.length],
        count: cnt,
        desc: `in ${cfg.col}`,
        isActive: isCardActive
      });
    });

    cardsData.forEach((c, idx) => {
      const cardEl = document.createElement("div");
      cardEl.className = `sub-metric-item ${c.isActive ? "active" : ""}`;

      const titleHtml = c.slotIdx === -1
        ? `<span style="overflow:hidden; text-overflow:ellipsis; white-space:nowrap;">${escapeHtml(c.title)}</span>`
        : `<select class="card-slot-picker" data-slot="${c.slotIdx}" title="คลิกเพื่อเปลี่ยนค่า (Value) ที่แสดงในการ์ดนี้">
            ${c.orderedValues.map(v => `<option value="${escapeHtml(v)}" ${v === c.val ? "selected" : ""}>${escapeHtml(v)}</option>`).join("")}
           </select>`;

      const descHtml = c.slotIdx === -1
        ? `<div class="sub-desc">${escapeHtml(c.desc)}</div>`
        : `<div class="sub-desc">
            <select class="card-col-picker" data-slot="${c.slotIdx}" title="คลิกเพื่อเปลี่ยนคอลัมน์ (Column) ของการ์ดใบนี้">
              ${sheetHeaders.map(h => `<option value="${escapeHtml(h)}" ${h === c.col ? "selected" : ""}>in ${escapeHtml(h)}</option>`).join("")}
            </select>
           </div>`;

      cardEl.innerHTML = `
        <div class="sub-top">
          ${titleHtml}
          <span class="status-tag ${c.tagClass}">${escapeHtml(c.tag)}</span>
        </div>
        <div class="sub-val-row">
          <strong>${c.count}</strong>
          <small>rows</small>
        </div>
        ${descHtml}
        <div class="dot-ruler" id="dynRuler_${idx}"></div>
      `;

      // เปลี่ยนค่า (Value) ภายในการ์ดใบนี้โดยเฉพาะ
      const slotPicker = cardEl.querySelector(".card-slot-picker");
      if (slotPicker) {
        slotPicker.addEventListener("click", (e) => e.stopPropagation());
        slotPicker.addEventListener("change", (e) => {
          e.stopPropagation();
          const sIdx = Number(slotPicker.dataset.slot);
          const nextConfigs = resolvedConfigs.map(rc => ({ col: rc.col, val: rc.val }));
          nextConfigs[sIdx].val = e.target.value;
          customCardConfigs = nextConfigs;
          saveCustomCardConfigs(activeTabName || "default", customCardConfigs);
          if (activeCardFilter && activeCardFilter.col === nextConfigs[sIdx].col) {
            activeCardFilter = { col: nextConfigs[sIdx].col, val: e.target.value };
          }
          renderAnalytics();
          renderTable();
          showToast(`เปลี่ยนการ์ดช่องที่ ${sIdx + 2} เป็น "${e.target.value}" แล้ว`);
        });
      }

      // เปลี่ยนคอลัมน์ (Column) ภายในการ์ดใบนี้แยกอิสระจากใบอื่น!
      const colPicker = cardEl.querySelector(".card-col-picker");
      if (colPicker) {
        colPicker.addEventListener("click", (e) => e.stopPropagation());
        colPicker.addEventListener("change", (e) => {
          e.stopPropagation();
          const sIdx = Number(colPicker.dataset.slot);
          const newCol = e.target.value;
          const newColInfo = getColumnValueCounts(newCol, scopedRows);
          const defaultValForNewCol = newColInfo.orderedValues[0] || "(ว่าง)";
          const nextConfigs = resolvedConfigs.map(rc => ({ col: rc.col, val: rc.val }));
          nextConfigs[sIdx] = { col: newCol, val: defaultValForNewCol };
          customCardConfigs = nextConfigs;
          saveCustomCardConfigs(activeTabName || "default", customCardConfigs);
          if (activeCardFilter) {
            activeCardFilter = { col: newCol, val: defaultValForNewCol };
          }
          renderAnalytics();
          renderTable();
          showToast(`เปลี่ยนคอลัมน์ของการ์ดช่องที่ ${sIdx + 2} เป็น "${newCol}" แล้ว`);
        });
      }

      cardEl.addEventListener("click", () => {
        if (c.slotIdx === -1) {
          activeCardFilter = null;
        } else {
          const isSame = activeCardFilter && activeCardFilter.col === c.col && activeCardFilter.val === c.val;
          activeCardFilter = isSame ? null : { col: c.col, val: c.val };
        }
        currentPage = 1;
        renderAnalytics();
        renderTable();
      });

      metricsGrid.appendChild(cardEl);
      renderDotRuler(`dynRuler_${idx}`, totalRows > 0 ? c.count / totalRows : 0.1);
    });
  }

  // Sky Blue Gradient Hero Card
  document.getElementById("heroCompletionRate").textContent = totalRows;
  document.getElementById("heroCompletionUnit").textContent = totalCols > 0 ? `rows across ${totalCols} columns` : "total records";
  document.getElementById("slaPendingPill").textContent = `${totalCols} Cols`;
  const effCutoff = getEffectiveCutoff();
  document.getElementById("slaSubText").textContent = isConnected
    ? (effCutoff > 0 && rowsData.length > effCutoff
        ? `Showing Row 1 to ${totalRows.toLocaleString()} of ${rowsData.length.toLocaleString()} total rows (auto-expanding on inserted rows).`
        : `Active sheet "${activeTabName || "Default"}" synced dynamically with ${totalCols} columns.`)
    : "Connect any Google Sheet URL or Web App URL to visualize live data.";

  const activeRatioPct = totalRows > 0 ? (filtered.length / totalRows) * 100 : 0;
  renderSlaEqualizer(activeRatioPct);

  renderThroughputWidget(filtered.length, totalRows);
  renderLatestRecordsPreview();

  // Card 3: Secondary Dimension Filter List
  const secListEl = document.getElementById("overviewTechList");
  secListEl.innerHTML = "";

  if (!isConnected || !selectedSecondaryCol) {
    document.getElementById("secondaryDimTitle").textContent = "Quick group filter";
    document.getElementById("secondaryDimSub").textContent = isConnected ? "Single dimension sheet" : "Connect sheet to view groups";
    secListEl.innerHTML = `<div style="font-size: 0.8rem; color: var(--ink-muted); padding: 12px 0;">${isConnected ? "All columns are displayed in the table below." : "Waiting for Google Sheet connection."}</div>`;
  } else {
    document.getElementById("secondaryDimTitle").textContent = `Filter by ${selectedSecondaryCol}`;
    document.getElementById("secondaryDimSub").textContent = "Click any item below to filter rows";

    const secCounts = {};
    scopedRows.forEach(r => {
      const v = String(r[selectedSecondaryCol] ?? "").trim() || "(ว่าง)";
      secCounts[v] = (secCounts[v] || 0) + 1;
    });

    Object.entries(secCounts)
      .sort((a, b) => b[1] - a[1])
      .slice(0, 3)
      .forEach(([val, cnt]) => {
        const chip = document.createElement("div");
        chip.className = `tech-pill-row ${selectedSecondaryValue === val ? "active" : ""}`;
        chip.innerHTML = `<strong>${escapeHtml(val)}</strong><span>${cnt} rows</span>`;
        chip.addEventListener("click", () => {
          selectedSecondaryValue = selectedSecondaryValue === val ? "ALL" : val;
          currentPage = 1;
          renderAnalytics();
          renderTable();
        });
        secListEl.appendChild(chip);
      });
  }

  renderSummaryView();
}

// ฟังก์ชันช่วยแปลงวันที่หลากหลายรูปแบบ (DD/MM/YY, DD/MM/YYYY, YYYY-MM-DD) ให้เป็น YYYY-MM สำหรับจัดกลุ่มรายเดือน
function extractYearMonth(rawDateStr) {
  const s = String(rawDateStr || "").trim();
  if (!s) return null;

  // Format: YYYY-MM-DD or YYYY/MM/DD
  let m = s.match(/^(\d{4})[-/](\d{1,2})[-/](\d{1,2})/);
  if (m) {
    let y = parseInt(m[1], 10);
    if (y > 2400) y -= 543; // แปลง พ.ศ. เป็น ค.ศ. เพื่อเรียงลำดับถูกต้อง
    return `${y}-${String(m[2]).padStart(2, "0")}`;
  }

  // Format: DD/MM/YYYY or DD-MM-YYYY or DD/MM/YY
  m = s.match(/^(\d{1,2})[-/](\d{1,2})[-/](\d{2,4})/);
  if (m) {
    const month = String(m[2]).padStart(2, "0");
    if (Number(month) < 1 || Number(month) > 12) return null;
    let y = parseInt(m[3], 10);
    if (y < 100) {
      // ถ้าเป็นเลขปี 2 หลัก เช่น 26 (ค.ศ. 2026) หรือ 69 (พ.ศ. 2569 -> 2026)
      y = y >= 50 ? (2500 + y - 543) : (2000 + y);
    } else if (y > 2400) {
      y -= 543;
    }
    return `${y}-${month}`;
  }

  return null;
}

function renderSummaryView() {
  const scopedRows = getScopedRows();
  const totalRows = scopedRows.length;
  const totalCols = sheetHeaders.length;

  const pSelect = document.getElementById("sumPrimaryColSelect");
  const sSelect = document.getElementById("sumSecondaryColSelect");
  const dSelect = document.getElementById("sumDateColSelect");
  const highlightsGrid = document.getElementById("summaryHighlightsGrid");
  const monthlyChart = document.getElementById("sumMonthlyChart");
  const numericList = document.getElementById("sumNumericStatsList");
  const pRankList = document.getElementById("sumPrimaryRankList");
  const sRankList = document.getElementById("sumSecondaryRankList");

  if (!highlightsGrid || !pSelect || !sSelect || !dSelect) return;

  if (!isConnected || totalCols === 0 || totalRows === 0) {
    pSelect.innerHTML = `<option value="">Primary Column</option>`;
    sSelect.innerHTML = `<option value="">Secondary Column</option>`;
    dSelect.innerHTML = `<option value="">Date Column</option>`;
    highlightsGrid.innerHTML = `
      <div class="sum-stat-card sky-highlight"><span class="sum-stat-label">Total Records</span><strong class="sum-stat-value">0</strong><span class="sum-stat-sub">Connect Google Sheet</span></div>
      <div class="sum-stat-card"><span class="sum-stat-label">Top Category</span><strong class="sum-stat-value">-</strong><span class="sum-stat-sub">No data</span></div>
      <div class="sum-stat-card"><span class="sum-stat-label">Secondary Leader</span><strong class="sum-stat-value">-</strong><span class="sum-stat-sub">No data</span></div>
      <div class="sum-stat-card"><span class="sum-stat-label">Peak Month</span><strong class="sum-stat-value">-</strong><span class="sum-stat-sub">No data</span></div>
    `;
    monthlyChart.innerHTML = `<div style="width:100%; text-align:center; color:var(--ink-muted); font-size:0.84rem; align-self:center;">ยังไม่มีข้อมูลสำหรับสร้างกราฟรายเดือน</div>`;
    numericList.innerHTML = `<div style="color:var(--ink-muted); font-size:0.84rem; padding:12px 0;">ยังไม่มีข้อมูลตัวเลขในชีต</div>`;
    pRankList.innerHTML = `<div style="color:var(--ink-muted); font-size:0.84rem; padding:12px 0;">เชื่อมต่อ Google Sheet เพื่อดูอันดับสรุปยอด</div>`;
    sRankList.innerHTML = `<div style="color:var(--ink-muted); font-size:0.84rem; padding:12px 0;">เชื่อมต่อ Google Sheet เพื่อดูอันดับสรุปยอด</div>`;
    return;
  }

  // เลือกคอลัมน์เริ่มต้นอัตโนมัติสำหรับหน้า Summary ถ้ายังไม่เคยเลือก
  if (!sumPrimaryCol || !sheetHeaders.includes(sumPrimaryCol)) {
    const prio1 = sheetHeaders.find(h => /(status|สถานะ|equipment|type|category|เครื่องมือ|ประเภท)/i.test(h));
    sumPrimaryCol = prio1 || selectedGroupCol || sheetHeaders[0];
  }
  if (!sumSecondaryCol || !sheetHeaders.includes(sumSecondaryCol)) {
    const prio2 = sheetHeaders.find(h => h !== sumPrimaryCol && /(customer|company|ลูกค้า|บริษัท|sales|ช่าง|tech|มอบหมาย|brand|แผนก)/i.test(h));
    sumSecondaryCol = prio2 || sheetHeaders.find(h => h !== sumPrimaryCol) || sheetHeaders[0];
  }
  if (!sumDateCol || !sheetHeaders.includes(sumDateCol)) {
    const prioDate = sheetHeaders.find(h => /(date|วันที่|กำหนด|time)/i.test(h));
    sumDateCol = prioDate || sheetHeaders[0];
  }

  pSelect.innerHTML = sheetHeaders.map(h => `<option value="${escapeHtml(h)}" ${h === sumPrimaryCol ? "selected" : ""}>หลัก: ${escapeHtml(h)}</option>`).join("");
  sSelect.innerHTML = sheetHeaders.map(h => `<option value="${escapeHtml(h)}" ${h === sumSecondaryCol ? "selected" : ""}>รอง: ${escapeHtml(h)}</option>`).join("");
  dSelect.innerHTML = sheetHeaders.map(h => `<option value="${escapeHtml(h)}" ${h === sumDateCol ? "selected" : ""}>วันที่: ${escapeHtml(h)}</option>`).join("");

  // 1. คำนวณอันดับของ Primary & Secondary Columns
  const buildRanking = (colName) => {
    const map = {};
    scopedRows.forEach(r => {
      const v = String(r[colName] ?? "").trim();
      if (!v || v === "-") return;
      map[v] = (map[v] || 0) + 1;
    });
    return Object.entries(map).sort((a, b) => b[1] - a[1]);
  };

  const pRank = buildRanking(sumPrimaryCol);
  const sRank = buildRanking(sumSecondaryCol);

  // 2. คำนวณแนวโน้มรายเดือนจาก sumDateCol
  const monthMap = {};
  scopedRows.forEach(r => {
    const ym = extractYearMonth(r[sumDateCol]);
    if (ym) monthMap[ym] = (monthMap[ym] || 0) + 1;
  });
  const sortedMonths = Object.entries(monthMap).sort((a, b) => a[0].localeCompare(b[0]));
  const peakMonth = [...sortedMonths].sort((a, b) => b[1] - a[1])[0];

  // 3. อัปเดต 4 Executive Highlight Cards
  const topP = pRank[0];
  const topS = sRank[0];
  highlightsGrid.innerHTML = `
    <div class="sum-stat-card sky-highlight">
      <span class="sum-stat-label">ขอบเขตข้อมูลที่วิเคราะห์ (Scoped Rows)</span>
      <strong class="sum-stat-value">${totalRows.toLocaleString()} รายการ</strong>
      <span class="sum-stat-sub">จากทั้งหมด ${rowsData.length.toLocaleString()} แถว (${totalCols} คอลัมน์)</span>
    </div>
    <div class="sum-stat-card">
      <span class="sum-stat-label">อันดับ 1 ใน "${escapeHtml(sumPrimaryCol)}"</span>
      <strong class="sum-stat-value" title="${topP ? escapeHtml(topP[0]) : "-"}">${topP ? escapeHtml(topP[0]) : "-"}</strong>
      <span class="sum-stat-sub">${topP ? `${topP[1].toLocaleString()} รายการ (${Math.round((topP[1] / totalRows) * 100)}%)` : "ไม่พบข้อมูล"}</span>
    </div>
    <div class="sum-stat-card">
      <span class="sum-stat-label">อันดับ 1 ใน "${escapeHtml(sumSecondaryCol)}"</span>
      <strong class="sum-stat-value" title="${topS ? escapeHtml(topS[0]) : "-"}">${topS ? escapeHtml(topS[0]) : "-"}</strong>
      <span class="sum-stat-sub">${topS ? `${topS[1].toLocaleString()} รายการ (${Math.round((topS[1] / totalRows) * 100)}%)` : "ไม่พบข้อมูล"}</span>
    </div>
    <div class="sum-stat-card">
      <span class="sum-stat-label">เดือนที่ปริมาณงานสูงสุด (${escapeHtml(sumDateCol)})</span>
      <strong class="sum-stat-value">${peakMonth ? escapeHtml(peakMonth[0]) : "-"}</strong>
      <span class="sum-stat-sub">${peakMonth ? `${peakMonth[1].toLocaleString()} รายการในเดือนนี้` : "ไม่พบรูปแบบวันที่ในคอลัมน์นี้"}</span>
    </div>
  `;

  // 4. วาดกราฟแท่งรายเดือน (Monthly Trend)
  document.getElementById("sumMonthlyTitle").textContent = `แนวโน้มปริมาณข้อมูลรายเดือน (${sumDateCol})`;
  document.getElementById("sumMonthsCountBadge").textContent = `${sortedMonths.length} Months`;
  if (sortedMonths.length === 0) {
    monthlyChart.innerHTML = `<div style="width:100%; text-align:center; color:var(--ink-muted); font-size:0.84rem; align-self:center;">ไม่พบข้อมูลวันที่ในคอลัมน์ "${escapeHtml(sumDateCol)}" ลองเปลี่ยนเลือกคอลัมน์วันที่ด้านบน</div>`;
  } else {
    const recentMonths = sortedMonths.slice(-12); // แสดงสูงสุด 12 เดือนล่าสุด
    const maxM = Math.max(1, ...recentMonths.map(x => x[1]));
    monthlyChart.innerHTML = recentMonths.map(([ym, cnt]) => {
      const barH = Math.max(12, Math.round((cnt / maxM) * 135));
      return `
        <div class="m-bar-group" title="${ym}: ${cnt.toLocaleString()} รายการ">
          <span class="m-bar-val">${cnt.toLocaleString()}</span>
          <div class="m-bar-col" style="height: ${barH}px;"></div>
          <span class="m-bar-label">${escapeHtml(ym)}</span>
        </div>
      `;
    }).join("");
  }

  // 5. ตรวจจับคอลัมน์ตัวเลขและคำนวณ Sum / Avg / Min / Max อัตโนมัติ
  const numericCols = [];
  sheetHeaders.forEach(col => {
    // ข้ามคอลัมน์วันที่หรือรหัสใบงานที่มีขีด
    if (/(date|วันที่|กำหนด|no\.|id|serial|s\/n|เบอร์|โทร)/i.test(col)) return;
    const nums = [];
    scopedRows.forEach(r => {
      const raw = String(r[col] ?? "").replace(/,/g, "").trim();
      if (raw !== "" && /^-?\d+(\.\d+)?$/.test(raw)) {
        nums.push(parseFloat(raw));
      }
    });
    if (nums.length >= Math.max(3, Math.floor(totalRows * 0.15))) {
      const sum = nums.reduce((a, b) => a + b, 0);
      const avg = sum / nums.length;
      const min = Math.min(...nums);
      const max = Math.max(...nums);
      numericCols.push({ col, count: nums.length, sum, avg, min, max });
    }
  });

  document.getElementById("sumNumericCountBadge").textContent = `${numericCols.length} Numeric Cols`;
  if (numericCols.length === 0) {
    numericList.innerHTML = `<div style="color:var(--ink-muted); font-size:0.84rem; padding:14px 0;">ไม่พบคอลัมน์ตัวเลขล้วนสำหรับคำนวณผลรวม (แสดงสถิติจำนวนนับในตารางด้านล่างแทน)</div>`;
  } else {
    numericList.innerHTML = numericCols.map(item => `
      <div class="num-stat-row">
        <span class="num-stat-col-name">${escapeHtml(item.col)}</span>
        <div class="num-stat-pills">
          <span class="num-pill">Sum: <strong>${item.sum.toLocaleString(undefined, { maximumFractionDigits: 2 })}</strong></span>
          <span class="num-pill">Avg: <strong>${item.avg.toLocaleString(undefined, { maximumFractionDigits: 2 })}</strong></span>
          <span class="num-pill">Min: <strong>${item.min.toLocaleString()}</strong></span>
          <span class="num-pill">Max: <strong>${item.max.toLocaleString()}</strong></span>
        </div>
      </div>
    `).join("");
  }

  // 6. วาดตารางอันดับ Top Breakdown ทั้ง 2 คอลัมน์ (คลิกเพื่อกรองตารางจริงได้ทันที)
  const renderRankContainer = (containerEl, rankEntries, colName) => {
    containerEl.innerHTML = "";
    if (rankEntries.length === 0) {
      containerEl.innerHTML = `<div style="color:var(--ink-muted); font-size:0.84rem; padding:12px 0;">ไม่พบข้อมูลในคอลัมน์นี้</div>`;
      return;
    }
    const maxCnt = rankEntries[0][1];
    rankEntries.slice(0, 15).forEach(([val, cnt], idx) => {
      const pctOfTotal = ((cnt / totalRows) * 100).toFixed(1);
      const barWidth = Math.max(4, Math.round((cnt / maxCnt) * 100));
      const rowDiv = document.createElement("div");
      rowDiv.className = "rank-row-item";
      rowDiv.title = `คลิกเพื่อกรองตารางเฉพาะ "${val}"`;
      rowDiv.innerHTML = `
        <div class="rank-row-top">
          <div class="rank-name-wrap">
            <span class="rank-num">${idx + 1}</span>
            <span class="rank-title">${escapeHtml(val)}</span>
          </div>
          <span class="rank-count-meta">${cnt.toLocaleString()} (${pctOfTotal}%)</span>
        </div>
        <div class="rank-bar-track">
          <div class="rank-bar-fill" style="width: ${barWidth}%;"></div>
        </div>
      `;
      rowDiv.addEventListener("click", () => {
        selectedGroupCol = colName;
        selectedGroupValue = val;
        currentPage = 1;
        if (!isDirectoryExpanded) {
          isDirectoryExpanded = true;
          safeSetLocal("CALIB_DIR_EXPANDED", "true");
          applyDirectoryCollapseUI();
        }
        renderAnalytics();
        renderTable();
        document.getElementById("mainJobTableSection").scrollIntoView({ behavior: "smooth" });
        showToast(`กรองตารางเฉพาะ "${val}" (${cnt.toLocaleString()} รายการ) แล้ว`);
      });
      containerEl.appendChild(rowDiv);
    });
  };

  document.getElementById("sumPrimaryRankTitle").textContent = `สรุปตาม "${sumPrimaryCol}" (Top 15)`;
  document.getElementById("sumPrimaryUniqueBadge").textContent = `${pRank.length.toLocaleString()} รายการไม่ซ้ำ`;
  renderRankContainer(pRankList, pRank, sumPrimaryCol);

  document.getElementById("sumSecondaryRankTitle").textContent = `สรุปตาม "${sumSecondaryCol}" (Top 15)`;
  document.getElementById("sumSecondaryUniqueBadge").textContent = `${sRank.length.toLocaleString()} รายการไม่ซ้ำ`;
  renderRankContainer(sRankList, sRank, sumSecondaryCol);
}

function getFilteredAndSortedRows() {
  const scopedRows = getScopedRows();
  const filtered = scopedRows.filter(row => {
    if (activeCardFilter && activeCardFilter.col) {
      const val = String(row[activeCardFilter.col] ?? "").trim() || "(ว่าง)";
      if (val !== activeCardFilter.val) return false;
    }

    if (selectedSecondaryCol && selectedSecondaryValue !== "ALL") {
      const val2 = String(row[selectedSecondaryCol] ?? "").trim() || "(ว่าง)";
      if (val2 !== selectedSecondaryValue) return false;
    }

    const q = currentSearch.toLowerCase().trim();
    if (q) {
      const matchedAnyCol = sheetHeaders.some(h =>
        String(row[h] ?? "").toLowerCase().includes(q)
      );
      if (!matchedAnyCol) return false;
    }

    return true;
  });

  if (sortState.column && sheetHeaders.includes(sortState.column)) {
    filtered.sort((a, b) => {
      const valA = String(a[sortState.column] ?? "");
      const valB = String(b[sortState.column] ?? "");
      const cmp = valA.localeCompare(valB, "th", { numeric: true, sensitivity: "base" });
      return sortState.direction === "asc" ? cmp : -cmp;
    });
  } else {
    // ค่าเริ่มต้น: เรียงแถวล่างสุดของ Sheet (ข้อมูลล่าสุด) ขึ้นแสดงด้านบนสุด
    filtered.reverse();
  }

  return filtered;
}

function getBadgeToneClass(val) {
  const str = String(val || "").trim();
  let hash = 0;
  for (let i = 0; i < str.length; i++) {
    hash = str.charCodeAt(i) + ((hash << 5) - hash);
  }
  return `badge-tone-${Math.abs(hash) % 5}`;
}

function renderTable() {
  const thead = document.getElementById("dynamicTableHead");
  const tbody = document.getElementById("jobTableBody");
  thead.innerHTML = "";
  tbody.innerHTML = "";

  const filtered = getFilteredAndSortedRows();
  const totalFiltered = filtered.length;
  const totalPages = Math.max(1, Math.ceil(totalFiltered / ROWS_PER_PAGE));
  if (currentPage > totalPages) currentPage = totalPages;
  if (currentPage < 1) currentPage = 1;

  const startIdx = (currentPage - 1) * ROWS_PER_PAGE;
  const endIdx = Math.min(startIdx + ROWS_PER_PAGE, totalFiltered);
  const pageRows = filtered.slice(startIdx, endIdx);

  const effLimit = getEffectiveCutoff();
  const scopeNote = (effLimit > 0 && rowsData.length > effLimit) ? ` (Row 1–${effLimit.toLocaleString()})` : "";
  document.getElementById("filteredCountBadge").textContent = totalFiltered > 0
    ? `Page ${currentPage}/${totalPages} (${startIdx + 1}–${endIdx} of ${totalFiltered}${scopeNote})`
    : `Showing 0 of ${getScopedRows().length} rows`;

  const canEditRows = Boolean(isAdminMode && connectionMode === "apps_script");
  const paginationBar = document.getElementById("paginationBar");

  const topSliderWrap = document.getElementById("topTableSliderWrap");
  if (!connectionSource || !isConnected) {
    if (paginationBar) paginationBar.style.display = "none";
    if (topSliderWrap) topSliderWrap.style.display = "none";
    thead.innerHTML = `<tr><th>การเชื่อมต่อ Google Sheet</th></tr>`;
    tbody.innerHTML = `
      <tr>
        <td class="empty-row">
          <div class="empty-connect-box">
            <p>${!connectionSource ? "ยังไม่ได้เชื่อมต่อฐานข้อมูล Google Sheet (รองรับทุกตาราง ไม่จำกัดจำนวนคอลัมน์และแถว)" : "กำลังดึงโครงสร้างคอลัมน์และข้อมูลจาก Google Sheet..."}</p>
            <button type="button" class="cta-dark-pill" id="inlineConnectBtn">เชื่อมต่อ Google Sheet</button>
          </div>
        </td>
      </tr>
    `;
    const inlineBtn = tbody.querySelector("#inlineConnectBtn");
    if (inlineBtn) {
      inlineBtn.addEventListener("click", () => {
        document.getElementById("apiUrlInput").value = connectionSource;
        document.getElementById("optionalTabInput").value = activeTabName;
        document.getElementById("apiModal").classList.add("open");
      });
    }
    return;
  }

  if (sheetHeaders.length === 0) {
    if (paginationBar) paginationBar.style.display = "none";
    thead.innerHTML = `<tr><th>Empty Sheet</th></tr>`;
    tbody.innerHTML = `<tr><td class="empty-row">ไม่พบหัวตารางในชีตนี้ กรุณาเพิ่มหัวคอลัมน์ในแถวที่ 1 ของ Google Sheet</td></tr>`;
    return;
  }

  const activeCols = visibleTableHeaders.length > 0 ? visibleTableHeaders : sheetHeaders;
  const badgeEl = document.getElementById("visibleColsCountBadge");
  if (badgeEl) badgeEl.textContent = `${activeCols.length}/${sheetHeaders.length}`;

  // สร้างหัวตาราง (<thead>) ตามคอลัมน์ที่ผู้ใช้เลือกให้แสดง
  const headerTr = document.createElement("tr");
  activeCols.forEach(colName => {
    const th = document.createElement("th");
    th.className = "sortable";
    const ind = sortState.column === colName ? (sortState.direction === "asc" ? "↑" : "↓") : "↕";
    th.innerHTML = `${escapeHtml(colName)} <span class="sort-ind">${ind}</span>`;
    th.addEventListener("click", () => {
      if (sortState.column === colName) {
        sortState.direction = sortState.direction === "asc" ? "desc" : "asc";
      } else {
        sortState.column = colName;
        sortState.direction = "asc";
      }
      renderTable();
    });
    headerTr.appendChild(th);
  });

  if (canEditRows) {
    const actionTh = document.createElement("th");
    actionTh.className = "text-center";
    actionTh.textContent = "จัดการ";
    headerTr.appendChild(actionTh);
  }
  thead.appendChild(headerTr);

  if (filtered.length === 0) {
    if (paginationBar) paginationBar.style.display = "none";
    if (topSliderWrap) topSliderWrap.style.display = "none";
    const colSpan = activeCols.length + (canEditRows ? 1 : 0);
    tbody.innerHTML = `<tr><td colspan="${colSpan}" class="empty-row">${rowsData.length === 0 ? "ยังไม่มีแถวข้อมูลในชีตนี้" : "ไม่พบข้อมูลที่ตรงกับเงื่อนไขการค้นหา"}</td></tr>`;
    return;
  }

  // เตรียมตัวเลือกค่าที่มีอยู่แล้วในคอลัมน์หลัก สำหรับทำ Dropdown เปลี่ยนค่าเร็วในโหมด Admin
  const groupOptions = selectedGroupCol
    ? Array.from(new Set(rowsData.map(r => String(r[selectedGroupCol] ?? "").trim()).filter(Boolean)))
    : [];

  pageRows.forEach(row => {
    const tr = document.createElement("tr");

    activeCols.forEach((col, cIdx) => {
      const td = document.createElement("td");
      const cellVal = String(row[col] ?? "");

      if (cIdx === 0) {
        td.className = "mono-sky";
        td.textContent = cellVal || "-";
      } else if (col === selectedGroupCol && groupOptions.length >= 2 && groupOptions.length <= 12) {
        const toneClass = getBadgeToneClass(cellVal);
        if (canEditRows) {
          const sel = document.createElement("select");
          sel.className = `inline-cell-select ${toneClass}`;
          sel.innerHTML = groupOptions.map(opt =>
            `<option value="${escapeHtml(opt)}" ${opt === cellVal ? "selected" : ""}>${escapeHtml(opt)}</option>`
          ).join("");
          sel.addEventListener("change", async (e) => {
            const newVal = e.target.value;
            row[col] = newVal;
            renderAnalytics();
            renderTable();
            await syncChangeToSheet("updateCell", {
              _rowIndex: row._rowIndex,
              column: col,
              value: newVal
            });
          });
          td.appendChild(sel);
        } else {
          td.innerHTML = `<span class="status-readonly-badge ${toneClass}">${escapeHtml(cellVal || "-")}</span>`;
        }
      } else {
        td.textContent = cellVal;
      }

      tr.appendChild(td);
    });

    if (canEditRows) {
      const actionTd = document.createElement("td");
      actionTd.className = "text-center";
      actionTd.style.whiteSpace = "nowrap";
      actionTd.innerHTML = `
        <div class="action-btn-group">
          <button type="button" class="icon-btn edit-btn" title="แก้ไขแถวข้อมูล" aria-label="แก้ไขแถวข้อมูล">
            <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M11 4H4a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h14a2 2 0 0 0 2-2v-7"/><path d="M18.5 2.5a2.121 2.121 0 0 1 3 3L12 15l-4 1 1-4 9.5-9.5z"/></svg>
          </button>
          <button type="button" class="icon-btn delete delete-btn" title="ลบแถวข้อมูล" aria-label="ลบแถวข้อมูล">
            <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="3 6 5 6 21 6"/><path d="M19 6v14a2 2 0 0 1-2 2H7a2 2 0 0 1-2-2V6m3 0V4a2 2 0 0 1 2-2h4a2 2 0 0 1 2 2v2"/></svg>
          </button>
        </div>
      `;
      actionTd.querySelector(".edit-btn").addEventListener("click", () => openDynamicRowModal(row));
      actionTd.querySelector(".delete-btn").addEventListener("click", () => openDeleteConfirmModal(row));
      tr.appendChild(actionTd);
    }

    tbody.appendChild(tr);
  });

  renderPaginationControls(totalFiltered, totalPages, startIdx, endIdx);
  syncTopTableSlider();
}

function syncTopTableSlider() {
  const wrap = document.getElementById("topTableSliderWrap");
  const topScroll = document.getElementById("topTableScroll");
  const spacer = document.getElementById("topTableScrollSpacer");
  const mainScroll = document.getElementById("mainTableScroll");
  const tableEl = document.getElementById("mainDataTable");

  if (!wrap || !topScroll || !spacer || !mainScroll || !tableEl) return;

  requestAnimationFrame(() => {
    const tableWidth = tableEl.scrollWidth;
    const containerWidth = mainScroll.clientWidth;

    if (isConnected && rowsData.length > 0 && tableWidth > containerWidth + 4) {
      wrap.style.display = "flex";
      spacer.style.width = `${tableWidth}px`;
      topScroll.scrollLeft = mainScroll.scrollLeft;
    } else {
      wrap.style.display = "none";
    }
  });
}

function renderPaginationControls(totalFiltered, totalPages, startIdx, endIdx) {
  const bar = document.getElementById("paginationBar");
  const infoEl = document.getElementById("paginationInfo");
  const numbersWrap = document.getElementById("pageNumbersWrap");
  const firstBtn = document.getElementById("firstPageBtn");
  const prevBtn = document.getElementById("prevPageBtn");
  const nextBtn = document.getElementById("nextPageBtn");
  const lastBtn = document.getElementById("lastPageBtn");

  if (!bar || !infoEl || !numbersWrap) return;

  bar.style.display = "flex";
  infoEl.textContent = `แสดงแถวที่ ${startIdx + 1} - ${endIdx} จากทั้งหมด ${totalFiltered.toLocaleString()} รายการ (หน้า ${currentPage} / ${totalPages})`;

  firstBtn.disabled = currentPage <= 1;
  prevBtn.disabled = currentPage <= 1;
  nextBtn.disabled = currentPage >= totalPages;
  lastBtn.disabled = currentPage >= totalPages;

  numbersWrap.innerHTML = "";
  const pagesToShow = [];
  for (let p = 1; p <= totalPages; p++) {
    if (p === 1 || p === totalPages || (p >= currentPage - 2 && p <= currentPage + 2)) {
      pagesToShow.push(p);
    } else if (pagesToShow[pagesToShow.length - 1] !== "...") {
      pagesToShow.push("...");
    }
  }

  pagesToShow.forEach(item => {
    if (item === "...") {
      const span = document.createElement("span");
      span.className = "page-ellipsis";
      span.textContent = "...";
      numbersWrap.appendChild(span);
    } else {
      const btn = document.createElement("button");
      btn.type = "button";
      btn.className = `page-btn ${item === currentPage ? "active" : ""}`;
      btn.textContent = item;
      btn.addEventListener("click", () => {
        currentPage = item;
        renderTable();
        document.getElementById("mainJobTableSection").scrollIntoView({ behavior: "smooth" });
      });
      numbersWrap.appendChild(btn);
    }
  });
}

// แปลงผลลัพธ์จาก Google Visualization API (gviz) กรณีใช้ลิงก์ Google Sheet โดยตรง
function parseGvizResponse(rawText) {
  const match = rawText.match(/google\.visualization\.Query\.setResponse\(([\s\S]+)\);?\s*$/);
  if (!match) throw new Error("Cannot parse Google Sheet response (ตรวจสอบว่าเปิดแชร์เป็น Anyone with the link แล้ว)");
  const json = JSON.parse(match[1]);
  if (json.status === "error") {
    throw new Error(json.errors?.[0]?.detailed_message || "Google Sheet access error");
  }

  const table = json.table;
  const cols = table.cols || [];
  const rows = table.rows || [];

  // เช็คว่าแถวแรกเป็น header หรือ cols มี label อยู่แล้ว
  let headers = cols.map((c, idx) => String(c.label || "").trim());
  let startRowIdx = 0;

  if (headers.every(h => h === "") && rows.length > 0) {
    headers = (rows[0].c || []).map((cell, idx) => String(cell?.f ?? cell?.v ?? "").trim() || `Column_${idx + 1}`);
    startRowIdx = 1;
  } else {
    headers = headers.map((h, idx) => h || `Column_${idx + 1}`);
  }

  const parsedRows = [];
  for (let r = startRowIdx; r < rows.length; r++) {
    const cells = rows[r].c || [];
    const obj = { _rowIndex: r + 1 };
    let hasValue = false;
    headers.forEach((h, cIdx) => {
      const cell = cells[cIdx];
      const val = cell ? (cell.f !== undefined && cell.f !== null ? String(cell.f) : (cell.v !== null && cell.v !== undefined ? String(cell.v) : "")) : "";
      if (val.trim() !== "") hasValue = true;
      obj[h] = val;
    });
    if (hasValue) parsedRows.push(obj);
  }

  return { headers, data: parsedRows };
}

function updateTabSelectorUI() {
  const tabSelect = document.getElementById("sheetTabSelect");
  if (!tabSelect) return;

  if (availableTabs.length > 1) {
    tabSelect.style.display = "inline-block";
    tabSelect.innerHTML = availableTabs.map(t =>
      `<option value="${escapeHtml(t)}" ${t === activeTabName ? "selected" : ""}>Tab: ${escapeHtml(t)}</option>`
    ).join("");
  } else {
    tabSelect.style.display = "none";
  }
}

// ดึงข้อมูลจาก Google Sheet (รองรับทั้ง Apps Script URL และ Direct Google Sheet Link)
async function fetchFromSheet(force = false) {
  if (!connectionSource || (isSavingToSheet && !force)) return;

  const target = parseConnectionTarget(connectionSource, activeTabName);
  if (target.mode === "none" || target.mode === "invalid") {
    isConnected = false;
    connectionMode = "none";
    updateConnectionState("Invalid URL", "offline");
    return;
  }

  try {
    updateConnectionState("Syncing...", "syncing");

    if (target.mode === "apps_script") {
      connectionMode = "apps_script";
      const sep = target.execUrl.includes("?") ? "&" : "?";
      const tabParam = target.tabName ? `&sheet=${encodeURIComponent(target.tabName)}` : "";
      const url = `${target.execUrl}${sep}t=${Date.now()}${tabParam}`;

      const res = await fetch(url, { redirect: "follow" });
      const json = await res.json();

      if (json && json.status === "success" && Array.isArray(json.data)) {
        rowsData = json.data;
        availableTabs = Array.isArray(json.availableSheets) ? json.availableSheets : [];
        if (json.sheetName) activeTabName = json.sheetName;

        // ดึง headers จาก response หรือจาก keys ของข้อมูลแถวแรก
        if (Array.isArray(json.headers) && json.headers.length > 0) {
          sheetHeaders = json.headers;
        } else if (rowsData.length > 0) {
          sheetHeaders = Object.keys(rowsData[0]).filter(k => !k.startsWith("_"));
        } else {
          sheetHeaders = [];
        }
      } else {
        throw new Error(json?.message || "Invalid Apps Script response");
      }
    } else if (target.mode === "public_gviz") {
      connectionMode = "public_gviz";
      let gvizUrl = `https://docs.google.com/spreadsheets/d/${target.spreadsheetId}/gviz/tq?tqx=out:json&t=${Date.now()}`;
      if (target.tabName) {
        gvizUrl += `&sheet=${encodeURIComponent(target.tabName)}`;
      } else if (target.gid) {
        gvizUrl += `&gid=${encodeURIComponent(target.gid)}`;
      }

      const res = await fetch(gvizUrl);
      const text = await res.text();
      const parsed = parseGvizResponse(text);
      sheetHeaders = parsed.headers;
      rowsData = parsed.data;
      availableTabs = target.tabName ? [target.tabName] : [];
    }

    isConnected = true;
    if (rowCutoffLimit > 0 && rowCutoffBaselineFilled === 0) {
      rowCutoffBaselineFilled = rowsData.filter(isSubstantiveDataRow).length;
      safeSetLocal("GSHEET_ROW_CUTOFF_BASELINE_FILLED", String(rowCutoffBaselineFilled));
    }
    if (activeTabName) {
      document.getElementById("brandSheetTitle").textContent = activeTabName;
      document.getElementById("directoryTitle").textContent = `${activeTabName} directory`;
    }

    const timeStr = new Date().toLocaleTimeString("th-TH", { hour: "2-digit", minute: "2-digit" });
    updateConnectionState(`Synced ${timeStr}`, "online");
    updateTabSelectorUI();
    visibleTableHeaders = loadVisibleHeaders(activeTabName || "default", sheetHeaders);
    detectBestGroupingColumns();
    renderAnalytics();
    renderTable();
  } catch (err) {
    console.error("ดึงข้อมูลจาก Google Sheet ไม่สำเร็จ:", err);
    isConnected = false;
    sheetHeaders = [];
    rowsData = [];
    updateConnectionState("Connection failed", "offline");
    renderAnalytics();
    renderTable();
    showToast("เชื่อมต่อไม่สำเร็จ: กรุณาตรวจสอบลิงก์ หรือสิทธิ์การแชร์ (Anyone with the link)");
  }
}

async function syncChangeToSheet(action, payload) {
  if (!isConnected || connectionMode !== "apps_script") {
    showToast("การบันทึกกลับลง Sheet ต้องเชื่อมต่อผ่าน Google Apps Script Web App URL");
    return false;
  }
  const target = parseConnectionTarget(connectionSource, activeTabName);
  isSavingToSheet = true;
  updateConnectionState("Saving...", "syncing");
  try {
    const res = await fetch(target.execUrl, {
      method: "POST",
      redirect: "follow",
      headers: { "Content-Type": "text/plain;charset=utf-8" },
      body: JSON.stringify({ action, sheetName: activeTabName, payload })
    });
    let ok = true;
    try {
      const result = await res.json();
      if (result && result.status === "error") ok = false;
    } catch (_) {}

    if (ok) {
      const timeStr = new Date().toLocaleTimeString("th-TH", { hour: "2-digit", minute: "2-digit" });
      updateConnectionState(`Synced ${timeStr}`, "online");
      showToast("บันทึกข้อมูลลง Google Sheet เรียบร้อยแล้ว");
      setTimeout(() => {
        isSavingToSheet = false;
        fetchFromSheet(true);
      }, 1200);
      return true;
    } else {
      throw new Error("Sheet returned error");
    }
  } catch (err) {
    isSavingToSheet = false;
    setTimeout(() => fetchFromSheet(true), 1500);
    return false;
  }
}

// สร้างฟอร์มเพิ่ม/แก้ไขอัตโนมัติตามชื่อคอลัมน์จริงใน Google Sheet!
function openDynamicRowModal(rowObj = null) {
  if (!isAdminMode) {
    showToast("กรุณาเข้าสู่โหมด Admin ก่อนเพิ่มหรือแก้ไขข้อมูล");
    return;
  }
  if (!isConnected || connectionMode !== "apps_script") {
    showToast("กรุณาเชื่อมต่อผ่าน Apps Script Web App URL เพื่อเพิ่มหรือแก้ไขข้อมูลใน Sheet");
    return;
  }

  const modal = document.getElementById("jobFormModal");
  const title = document.getElementById("jobModalTitle");
  const fieldsContainer = document.getElementById("dynamicFormFields");
  fieldsContainer.innerHTML = "";

  editingRowObj = rowObj;
  title.textContent = rowObj
    ? `แก้ไขข้อมูล (${rowObj[sheetHeaders[0]] || `แถวที่ ${rowObj._rowIndex}`})`
    : "เพิ่มแถวข้อมูลใหม่ลง Google Sheet";

  sheetHeaders.forEach((col, idx) => {
    const group = document.createElement("div");
    group.className = sheetHeaders.length <= 4 ? "form-group full-width" : "form-group";

    const label = document.createElement("label");
    label.textContent = col;
    label.htmlFor = `dynField_${idx}`;

    const isDateCol = /(date|วันที่|กำหนด)/i.test(col);
    const input = document.createElement("input");
    input.id = `dynField_${idx}`;
    input.name = col;
    input.className = "clean-input";
    input.type = isDateCol ? "date" : "text";
    input.placeholder = `กรอก ${col}`;
    if (rowObj) {
      input.value = rowObj[col] ?? "";
    }

    group.appendChild(label);
    group.appendChild(input);
    fieldsContainer.appendChild(group);
  });

  modal.classList.add("open");
}

function openDeleteConfirmModal(rowObj) {
  if (!isAdminMode || connectionMode !== "apps_script") return;
  pendingDeleteRowObj = rowObj;
  const label = rowObj[sheetHeaders[0]] || `แถวที่ ${rowObj._rowIndex}`;
  document.getElementById("deleteTargetJobNo").textContent = label;
  document.getElementById("deleteConfirmModal").classList.add("open");
}

function exportFilteredToCSV() {
  if (rowsData.length === 0 || sheetHeaders.length === 0) return;
  const rows = getFilteredAndSortedRows();
  const colsToExport = visibleTableHeaders.length > 0 ? visibleTableHeaders : sheetHeaders;
  const csvLines = [
    colsToExport.map(h => `"${String(h).replace(/"/g, '""')}"`).join(","),
    ...rows.map(r => colsToExport.map(h => `"${String(r[h] ?? "").replace(/"/g, '""')}"`).join(","))
  ];
  const blob = new Blob(["\uFEFF" + csvLines.join("\n")], { type: "text/csv;charset=utf-8;" });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = `${activeTabName || "GoogleSheet"}_Export.csv`;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
  showToast(`ส่งออกข้อมูล ${rows.length} แถว (${sheetHeaders.length} คอลัมน์) เป็น CSV แล้ว`);
}

document.addEventListener("DOMContentLoaded", () => {
  // Smooth Intro Splash & Dashboard Rise-Up Controller
  const splashEl = document.getElementById("introSplash");
  const appShellEl = document.getElementById("appShell");
  const progressBarEl = document.getElementById("introProgressBar");
  const skipBtnEl = document.getElementById("skipIntroBtn");
  let introDismissed = false;

  const finishIntroSmoothly = () => {
    if (introDismissed) return;
    introDismissed = true;

    if (appShellEl) {
      appShellEl.classList.remove("intro-hidden-state");
      appShellEl.classList.add("intro-revealed");
    }

    if (splashEl) {
      splashEl.classList.add("is-exiting");
      splashEl.setAttribute("aria-hidden", "true");
      setTimeout(() => {
        splashEl.classList.add("is-done");
      }, 760);
    }
  };

  if (splashEl) {
    requestAnimationFrame(() => {
      if (progressBarEl) progressBarEl.style.width = "100%";
    });
    const autoTimer = setTimeout(finishIntroSmoothly, 1350);
    if (skipBtnEl) {
      skipBtnEl.addEventListener("click", () => {
        clearTimeout(autoTimer);
        finishIntroSmoothly();
      });
    }
  } else if (appShellEl) {
    appShellEl.classList.remove("intro-hidden-state");
    appShellEl.classList.add("intro-revealed");
  }

  // Activity tracker for 15-minute automatic session lock
  const markUserActivity = () => { lastActivityTime = Date.now(); };
  ["pointerdown", "keydown", "scroll", "mousemove"].forEach(ev => {
    document.addEventListener(ev, markUserActivity, { passive: true });
  });
  setInterval(() => {
    if (isGateAuthenticated() && (Date.now() - lastActivityTime > IDLE_TIMEOUT_MS)) {
      safeRemoveSession(GATE_SESSION_KEY);
      isAdminMode = false;
      safeRemoveSession("CALIB_IS_ADMIN");
      applyRoleUI();
      renderTable();
      setLoginGateVisible(true);
      showToast("ล็อกหน้าจออัตโนมัติเนื่องจากไม่มีการใช้งานเกิน 15 นาที");
    }
  }, 15000);

  const setSecretDisplayValue = (elId, secretVal, revealed = false) => {
    const el = document.getElementById(elId);
    if (!el) return;
    el.dataset.secret = secretVal || "";
    if (revealed && secretVal) {
      el.textContent = secretVal;
      el.classList.remove("masked-secret");
    } else {
      el.textContent = "••••••••••••••••";
      el.classList.add("masked-secret");
    }
  };

  // Initialize Sequential 2-Step Login Gate (Step 1: Password -> Step 2: iPhone / Authenticator OTP)
  ensureDefaultGatePasswordHash().then(() => {
    sync2faStatusUI();
    if (!isGateAuthenticated()) {
      setLoginGateVisible(true);
    }
  });

  // Live 30s TOTP countdown badge updater (never exposes the 6-digit OTP on screen)
  const refreshTotpTimers = () => {
    const secLeft = 30 - (Math.floor(Date.now() / 1000) % 30);
    ["otpCountdownBadge", "enrollCountdownBadge", "totpPreviewSec"].forEach(id => {
      const el = document.getElementById(id);
      if (el) el.textContent = `${secLeft}s`;
    });
  };
  refreshTotpTimers();
  setInterval(refreshTotpTimers, 1000);

  // STEP 1 Submit: Verify Password -> Advance to Step 2 (iPhone / Authenticator OTP screen)
  document.getElementById("gateStep1Form").addEventListener("submit", async (e) => {
    e.preventDefault();
    const errEl = document.getElementById("gateStep1Error");

    if (Date.now() < loginLockoutUntil) {
      const waitSec = Math.ceil((loginLockoutUntil - Date.now()) / 1000);
      if (errEl) {
        errEl.textContent = `กรอกผิดเกินกำหนด กรุณารอ ${waitSec} วินาทีแล้วลองใหม่อีกครั้ง`;
        errEl.style.display = "block";
      }
      return;
    }

    await ensureDefaultGatePasswordHash();
    const passVal = document.getElementById("gatePasswordInput").value;
    const inputHash = await hashPasswordWithSalt(passVal);
    const storedHash = safeGetLocal(GATE_PASS_HASH_KEY);
    const hasCustomPass = safeGetLocal("TMC_GATE_CUSTOM_PASS_V1") === "true";

    let passOk = (inputHash === storedHash);
    if (!passOk && passVal === "1234" && !hasCustomPass) {
      // Auto-heal stale or mismatched default hash without needing F12
      const healedHash = await hashPasswordWithSalt("1234");
      safeSetLocal(GATE_PASS_HASH_KEY, healedHash);
      passOk = true;
    }

    if (passOk) {
      step1PasswordVerified = true;
      if (errEl) errEl.style.display = "none";
      showLoginStep(2);
    } else {
      failedLoginAttempts += 1;
      if (failedLoginAttempts >= 5) {
        loginLockoutUntil = Date.now() + 30000;
        failedLoginAttempts = 0;
      }
      if (errEl) {
        errEl.textContent = "รหัสผ่านไม่ถูกต้อง";
        errEl.style.display = "block";
      }
    }
  });

  // Auto-sanitize OTP inputs (strip spaces/dashes when pasting from iPhone Passwords / Authenticator)
  ["gateOtpInput", "firstEnrollOtpInput", "confirmSetupOtpInput"].forEach(id => {
    const inp = document.getElementById(id);
    if (inp) {
      inp.addEventListener("input", () => {
        inp.value = inp.value.replace(/\D/g, "").slice(0, 6);
      });
    }
  });

  // Step 2A QR Code Drawer for adding a new phone / rotating secret after Step 1 password succeeds
  let step2ActiveQrSecret = "";
  let step2RotatingKey = false;

  const updateStep2VerifyForm = async () => {
    if (!step1PasswordVerified) {
      showLoginStep(1);
      return;
    }
    const errEl = document.getElementById("gateStep2Error");
    if (Date.now() < loginLockoutUntil) {
      const waitSec = Math.ceil((loginLockoutUntil - Date.now()) / 1000);
      if (errEl) {
        errEl.textContent = `กรอกผิดเกินกำหนด กรุณารอ ${waitSec} วินาทีแล้วลองใหม่อีกครั้ง`;
        errEl.style.display = "block";
      }
      return;
    }

    const otpVal = document.getElementById("gateOtpInput").value.trim();
    const secretToVerify = step2RotatingKey && step2ActiveQrSecret
      ? step2ActiveQrSecret
      : safeGetLocal(GATE_TOTP_SECRET_KEY);

    const otpOk = await verifyTotpCode(secretToVerify, otpVal, 1);

    if (otpOk) {
      if (step2RotatingKey && step2ActiveQrSecret) {
        safeSetLocal(GATE_TOTP_SECRET_KEY, step2ActiveQrSecret);
        safeSetLocal(GATE_2FA_ENABLED_KEY, "true");
        step2RotatingKey = false;
        step2ActiveQrSecret = "";
        sync2faStatusUI();
      }
      failedLoginAttempts = 0;
      step1PasswordVerified = false;
      if (errEl) errEl.style.display = "none";
      setLoginGateVisible(false);
      showToast("ยืนยันตัวตน 2 ชั้นสำเร็จ เข้าสู่ Dashboard แล้ว");
    } else {
      failedLoginAttempts += 1;
      if (failedLoginAttempts >= 5) {
        loginLockoutUntil = Date.now() + 30000;
        failedLoginAttempts = 0;
      }
      if (errEl) {
        errEl.textContent = "รหัส OTP 6 หลักไม่ถูกต้องหรือหมดอายุ กรุณาดูรหัสล่าสุดบนมือถือ";
        errEl.style.display = "block";
      }
    }
  };

  document.getElementById("toggleStep2QrBtn").addEventListener("click", () => {
    const drawer = document.getElementById("step2QrDrawer");
    if (!drawer) return;
    const willOpen = drawer.style.display === "none";
    drawer.style.display = willOpen ? "block" : "none";
    if (willOpen) {
      step2RotatingKey = false;
      step2ActiveQrSecret = safeGetLocal(GATE_TOTP_SECRET_KEY) || generateBase32Secret(16);
      document.getElementById("step2QrModeLabel").textContent = "Setup Key สำหรับสแกนเพิ่มเครื่องใหม่:";
      setSecretDisplayValue("step2VerifySecretDisplay", step2ActiveQrSecret, false);
      const revStep2Btn = document.getElementById("revealStep2KeyBtn");
      if (revStep2Btn) revStep2Btn.textContent = "แสดง Key";
      drawTotpQrMatrix(document.getElementById("step2VerifyQrCanvas"), buildOtpAuthUri(step2ActiveQrSecret));
      document.getElementById("step2QrHintText").textContent = "สแกนด้วยแอป Passwords บน iPhone หรือ Authenticator แล้วกรอกรหัส 6 หลักด้านบน";
    }
  });

  document.getElementById("revealStep2KeyBtn").addEventListener("click", () => {
    const el = document.getElementById("step2VerifySecretDisplay");
    const btn = document.getElementById("revealStep2KeyBtn");
    if (!el || !btn) return;
    const isNowRevealed = el.classList.contains("masked-secret");
    setSecretDisplayValue("step2VerifySecretDisplay", el.dataset.secret || step2ActiveQrSecret, isNowRevealed);
    btn.textContent = isNowRevealed ? "ซ่อน Key" : "แสดง Key";
  });

  document.getElementById("revealFirstEnrollKeyBtn").addEventListener("click", () => {
    const el = document.getElementById("firstEnrollSecretDisplay");
    const btn = document.getElementById("revealFirstEnrollKeyBtn");
    if (!el || !btn) return;
    const isNowRevealed = el.classList.contains("masked-secret");
    setSecretDisplayValue("firstEnrollSecretDisplay", el.dataset.secret || firstTimeEnrollSecret, isNowRevealed);
    btn.textContent = isNowRevealed ? "ซ่อน Key" : "แสดง Key";
  });

  document.getElementById("copyStep2KeyBtn").addEventListener("click", async () => {
    const keyVal = step2ActiveQrSecret || safeGetLocal(GATE_TOTP_SECRET_KEY) || "";
    if (!keyVal) return;
    try {
      await navigator.clipboard.writeText(keyVal);
      showToast("คัดลอก Setup Key แล้ว นำไปวางในแอป Passwords บน iPhone ได้เลย");
    } catch (_) {
      showToast(`Setup Key: ${keyVal}`);
    }
  });

  document.getElementById("rotateStep2KeyBtn").addEventListener("click", () => {
    step2RotatingKey = true;
    step2ActiveQrSecret = generateBase32Secret(16);
    document.getElementById("step2QrModeLabel").textContent = "Setup Key ใหม่ (ยืนยันด้วยรหัสจากเครื่องใหม่):";
    document.getElementById("step2VerifySecretDisplay").textContent = step2ActiveQrSecret;
    drawTotpQrMatrix(document.getElementById("step2VerifyQrCanvas"), buildOtpAuthUri(step2ActiveQrSecret));
    document.getElementById("step2QrHintText").textContent = "เมื่อสแกน Key ใหม่และกรอกรหัส 6 หลักสำเร็จ ระบบจะเปลี่ยนไปใช้ Key ใหม่ทันที";
    document.getElementById("gateOtpInput").value = "";
    document.getElementById("gateOtpInput").focus();
    showToast("สร้าง Setup Key ใหม่แล้ว กรุณาสแกนลงเครื่องใหม่และกรอกรหัส 6 หลัก");
  });

  // Back buttons from Step 2 to Step 1
  document.getElementById("gateBackToStep1Btn").addEventListener("click", () => showLoginStep(1));
  document.getElementById("gateEnrollBackBtn").addEventListener("click", () => showLoginStep(1));

  // STEP 2A Submit: Verify 6-digit OTP from bound iPhone / Authenticator (or newly scanned key)
  document.getElementById("gateStep2VerifyForm").addEventListener("submit", async (e) => {
    e.preventDefault();
    await updateStep2VerifyForm();
  });

  // STEP 2B Submit: First-Time 2FA Enrollment right after Step 1 Password
  document.getElementById("copyFirstEnrollKeyBtn").addEventListener("click", async () => {
    if (!firstTimeEnrollSecret) return;
    try {
      await navigator.clipboard.writeText(firstTimeEnrollSecret);
      showToast("คัดลอก Setup Key แล้ว นำไปวางในแอป Passwords บน iPhone ได้เลย");
    } catch (_) {
      showToast(`Setup Key: ${firstTimeEnrollSecret}`);
    }
  });

  document.getElementById("regenFirstEnrollKeyBtn").addEventListener("click", () => {
    firstTimeEnrollSecret = generateBase32Secret(16);
    const secEl = document.getElementById("firstEnrollSecretDisplay");
    if (secEl) secEl.textContent = firstTimeEnrollSecret;
    drawTotpQrMatrix(document.getElementById("firstEnrollQrCanvas"), buildOtpAuthUri(firstTimeEnrollSecret));
    const enrollInp = document.getElementById("firstEnrollOtpInput");
    if (enrollInp) {
      enrollInp.value = "";
      enrollInp.focus();
    }
    showToast("สร้าง Setup Key ใหม่แล้ว กรุณาสแกนลงมือถือและกรอกรหัส 6 หลัก");
  });

  document.getElementById("gateStep2EnrollForm").addEventListener("submit", async (e) => {
    e.preventDefault();
    const errEl = document.getElementById("gateEnrollError");
    if (!step1PasswordVerified || !firstTimeEnrollSecret) {
      showLoginStep(1);
      return;
    }

    const otpVal = document.getElementById("firstEnrollOtpInput").value.trim();
    const otpOk = await verifyTotpCode(firstTimeEnrollSecret, otpVal, 1);

    if (otpOk) {
      safeSetLocal(GATE_TOTP_SECRET_KEY, firstTimeEnrollSecret);
      safeSetLocal(GATE_2FA_ENABLED_KEY, "true");
      failedLoginAttempts = 0;
      step1PasswordVerified = false;
      safeSetSession(GATE_SESSION_KEY, "true");
      sync2faStatusUI();
      setLoginGateVisible(false);
      showToast("ผูกอุปกรณ์ 2FA และเข้าสู่ Dashboard เรียบร้อยแล้ว");
    } else {
      if (errEl) {
        errEl.textContent = "รหัส OTP 6 หลักไม่ตรงกับ QR Code นี้ กรุณาสแกนและกรอกรหัสล่าสุดจาก iPhone";
        errEl.style.display = "block";
      }
    }
  });

  document.getElementById("gateLogoutBtn").addEventListener("click", () => {
    safeRemoveSession(GATE_SESSION_KEY);
    isAdminMode = false;
    safeRemoveSession("CALIB_IS_ADMIN");
    applyRoleUI();
    renderTable();
    setLoginGateVisible(true);
    showToast("ออกจากระบบและล็อกหน้าจอแล้ว");
  });

  // Admin-Only TOTP QR Re-Binding Modal (Must be authenticated + in Admin Mode!)
  const setTotpSetupFeedback = (msg, type = "error") => {
    const fb = document.getElementById("totpSetupFeedback");
    if (!fb) return;
    fb.textContent = msg;
    fb.className = `modal-feedback ${type}`;
    fb.style.display = "block";
  };

  const openAdminTotpModal = () => {
    if (!isGateAuthenticated() || !isAdminMode) {
      showToast("เฉพาะผู้ดูแลระบบ (Admin Mode) เท่านั้นที่ตั้งค่า 2FA ได้");
      return;
    }
    pendingTotpCandidateSecret = is2faEnabled()
      ? safeGetLocal(GATE_TOTP_SECRET_KEY)
      : generateBase32Secret(20);

    document.getElementById("totpSecretDisplay").textContent = pendingTotpCandidateSecret;
    drawTotpQrMatrix(document.getElementById("totpQrCanvas"), buildOtpAuthUri(pendingTotpCandidateSecret));
    document.getElementById("confirmSetupOtpInput").value = "";
    const fb = document.getElementById("totpSetupFeedback");
    if (fb) fb.style.display = "none";

    document.getElementById("adminManageModal").classList.remove("open");
    document.getElementById("totpSetupModal").classList.add("open");
    setTimeout(() => document.getElementById("confirmSetupOtpInput").focus(), 60);
  };

  document.getElementById("openTotpSetupFromAdminBtn").addEventListener("click", openAdminTotpModal);
  document.getElementById("closeTotpModalBtn").addEventListener("click", () => {
    document.getElementById("totpSetupModal").classList.remove("open");
  });
  document.getElementById("cancelTotpSetupBtn").addEventListener("click", () => {
    document.getElementById("totpSetupModal").classList.remove("open");
  });

  document.getElementById("copyTotpKeyBtn").addEventListener("click", async () => {
    if (!pendingTotpCandidateSecret) return;
    try {
      await navigator.clipboard.writeText(pendingTotpCandidateSecret);
      showToast("คัดลอก Setup Key แล้ว นำไปวางในแอป Passwords บน iPhone ได้เลย");
    } catch (_) {
      showToast(`Setup Key: ${pendingTotpCandidateSecret}`);
    }
  });

  document.getElementById("regenTotpKeyBtn").addEventListener("click", () => {
    pendingTotpCandidateSecret = generateBase32Secret(20);
    document.getElementById("totpSecretDisplay").textContent = pendingTotpCandidateSecret;
    drawTotpQrMatrix(document.getElementById("totpQrCanvas"), buildOtpAuthUri(pendingTotpCandidateSecret));
    document.getElementById("confirmSetupOtpInput").value = "";
    setTotpSetupFeedback("สร้าง Setup Key ใหม่แล้ว กรุณาสแกนลง iPhone และกรอกรหัส 6 หลักเพื่อยืนยัน", "success");
  });

  document.getElementById("verifyAndEnableTotpForm").addEventListener("submit", async (e) => {
    e.preventDefault();
    if (!isGateAuthenticated() || !isAdminMode) return;
    const code = document.getElementById("confirmSetupOtpInput").value.trim();
    const ok = await verifyTotpCode(pendingTotpCandidateSecret, code, 1);
    if (!ok) {
      setTotpSetupFeedback("รหัส OTP 6 หลักไม่ตรงกับ QR Code นี้ กรุณาสแกนและลองกรอกรหัสล่าสุดจากมือถืออีกครั้ง", "error");
      return;
    }
    safeSetLocal(GATE_TOTP_SECRET_KEY, pendingTotpCandidateSecret);
    safeSetLocal(GATE_2FA_ENABLED_KEY, "true");
    sync2faStatusUI();
    setTotpSetupFeedback("ยืนยันสำเร็จ! อัปเดตการผูก 2FA เรียบร้อยแล้ว", "success");
    showToast("อัปเดตการผูก 2FA เรียบร้อยแล้ว");
    setTimeout(() => {
      document.getElementById("totpSetupModal").classList.remove("open");
    }, 700);
  });

  document.getElementById("disable2faBtn").addEventListener("click", () => {
    if (!isGateAuthenticated() || !isAdminMode) return;
    safeRemoveLocal(GATE_2FA_ENABLED_KEY);
    safeRemoveLocal(GATE_TOTP_SECRET_KEY);
    pendingTotpCandidateSecret = "";
    sync2faStatusUI();
    document.getElementById("totpSetupModal").classList.remove("open");
    showToast("รีเซ็ตการผูก 2FA แล้ว (การล็อกอินครั้งถัดไปจะให้สแกนผูกอุปกรณ์ใหม่ในขั้นที่ 2)");
  });

  // Admin-Only Change Login Password Modal
  const setPassFeedback = (msg, type = "error") => {
    const fb = document.getElementById("changeGatePassFeedback");
    if (!fb) return;
    fb.textContent = msg;
    fb.className = `modal-feedback ${type}`;
    fb.style.display = "block";
  };

  document.getElementById("openPassChangeFromAdminBtn").addEventListener("click", () => {
    if (!isGateAuthenticated() || !isAdminMode) {
      showToast("เฉพาะผู้ดูแลระบบ (Admin Mode) เท่านั้นที่เปลี่ยนรหัสผ่านได้");
      return;
    }
    document.getElementById("currentGatePassInput").value = "";
    document.getElementById("newGatePassInput").value = "";
    const fb = document.getElementById("changeGatePassFeedback");
    if (fb) fb.style.display = "none";
    document.getElementById("adminManageModal").classList.remove("open");
    document.getElementById("changeGatePassModal").classList.add("open");
    setTimeout(() => document.getElementById("currentGatePassInput").focus(), 60);
  });
  document.getElementById("closeChangeGatePassBtn").addEventListener("click", () => {
    document.getElementById("changeGatePassModal").classList.remove("open");
  });
  document.getElementById("cancelChangeGatePassBtn").addEventListener("click", () => {
    document.getElementById("changeGatePassModal").classList.remove("open");
  });

  document.getElementById("changeGatePassForm").addEventListener("submit", async (e) => {
    e.preventDefault();
    await ensureDefaultGatePasswordHash();
    const curPass = String(document.getElementById("currentGatePassInput").value || "");
    const newPass = String(document.getElementById("newGatePassInput").value || "");
    const curHash = await hashPasswordWithSalt(curPass);
    const storedHash = safeGetLocal(GATE_PASS_HASH_KEY);

    if (curHash !== storedHash) {
      setPassFeedback("รหัสผ่านปัจจุบันไม่ถูกต้อง (เริ่มต้นคือ 1234)", "error");
      showToast("รหัสผ่านปัจจุบันไม่ถูกต้อง");
      return;
    }
    if (newPass.trim().length < 4) {
      setPassFeedback("รหัสผ่านใหม่ต้องมีอย่างน้อย 4 ตัวอักษร", "error");
      showToast("รหัสผ่านใหม่ต้องมีอย่างน้อย 4 ตัวอักษร");
      return;
    }
    const newHash = await hashPasswordWithSalt(newPass.trim());
    safeSetLocal(GATE_PASS_HASH_KEY, newHash);
    safeSetLocal("TMC_GATE_CUSTOM_PASS_V1", "true");
    setPassFeedback("เปลี่ยนรหัสผ่านเรียบร้อยแล้ว สามารถใช้รหัสใหม่ล็อกอินได้ทันที", "success");
    showToast("เปลี่ยนรหัสผ่านเข้าสู่ระบบเรียบร้อยแล้ว");
    setTimeout(() => {
      document.getElementById("changeGatePassModal").classList.remove("open");
    }, 650);
  });

  // รองรับค่า URL เก่าจากเวอร์ชันก่อนหน้าอัตโนมัติ
  if (!connectionSource && safeGetLocal("GSHEET_API_URL")) {
    connectionSource = safeGetLocal("GSHEET_API_URL");
    safeSetLocal("GSHEET_SOURCE_INPUT", connectionSource);
  }

  const dateLabel = new Date().toLocaleDateString("en-US", { weekday: "long", day: "numeric", month: "long" }).toUpperCase();
  document.getElementById("currentDateEyebrow").textContent = `${dateLabel} • UNIVERSAL SHEETS SYNC`;

  applyRoleUI();
  applyDirectoryCollapseUI();
  renderAnalytics();
  renderTable();

  if (connectionSource) {
    fetchFromSheet(true);
    pollTimer = setInterval(() => fetchFromSheet(false), 10000);
  } else {
    updateConnectionState("Not connected", "offline");
  }

  // เลือกเปลี่ยน Tab ชีตย่อย
  document.getElementById("sheetTabSelect").addEventListener("change", (e) => {
    activeTabName = e.target.value;
    safeSetLocal("GSHEET_TAB_NAME", activeTabName);
    selectedGroupCol = "";
    activeCardFilter = null;
    selectedSecondaryCol = "";
    selectedSecondaryValue = "ALL";
    sumPrimaryCol = "";
    sumSecondaryCol = "";
    sumDateCol = "";
    currentPage = 1;
    fetchFromSheet(true);
  });

  // เลือกเปลี่ยนคอลัมน์หลักพร้อมกันทั้ง 3 การ์ด (หรือเลือกแยกแต่ละการ์ดได้เอง)
  document.getElementById("groupByColSelect").addEventListener("change", (e) => {
    selectedGroupCol = e.target.value;
    safeSetLocal("GSHEET_GROUP_COL", selectedGroupCol);
    const colInfo = getColumnValueCounts(selectedGroupCol, getScopedRows());
    customCardConfigs = [0, 1, 2].map(i => ({
      col: selectedGroupCol,
      val: colInfo.orderedValues[i] || colInfo.orderedValues[0] || "(ว่าง)"
    }));
    saveCustomCardConfigs(activeTabName || "default", customCardConfigs);
    activeCardFilter = null;
    currentPage = 1;
    renderAnalytics();
    renderTable();
  });

  // Modal กำหนดคอลัมน์และค่าที่จะโชว์ในการ์ดทั้ง 3 ช่องแบบแยกอิสระ
  const populateSingleSlotValueSelect = (valSelectId, colName, preferredVal = "") => {
    const valSel = document.getElementById(valSelectId);
    if (!valSel) return;
    const { counts, orderedValues } = getColumnValueCounts(colName, getScopedRows());
    const chosen = (preferredVal && orderedValues.includes(preferredVal)) ? preferredVal : (orderedValues[0] || "");
    valSel.innerHTML = orderedValues.map(v =>
      `<option value="${escapeHtml(v)}" ${v === chosen ? "selected" : ""}>${escapeHtml(v)} (${counts[v] || 0} rows)</option>`
    ).join("");
  };

  document.getElementById("customizeCardsBtn").addEventListener("click", () => {
    if (!isConnected || sheetHeaders.length === 0) return;
    const saved = loadCustomCardConfigs(activeTabName || "default");
    const defaultInfo = getColumnValueCounts(selectedGroupCol, getScopedRows());

    const slotPairs = [
      { colId: "cardSlot1ColSelect", valId: "cardSlot1Select", idx: 0 },
      { colId: "cardSlot2ColSelect", valId: "cardSlot2Select", idx: 1 },
      { colId: "cardSlot3ColSelect", valId: "cardSlot3Select", idx: 2 }
    ];

    slotPairs.forEach(({ colId, valId, idx }) => {
      const colSel = document.getElementById(colId);
      const s = saved[idx];
      const initCol = (s && s.col && sheetHeaders.includes(s.col)) ? s.col : selectedGroupCol;
      const initVal = (s && s.val) ? s.val : (defaultInfo.orderedValues[idx] || defaultInfo.orderedValues[0] || "");
      colSel.innerHTML = sheetHeaders.map(h =>
        `<option value="${escapeHtml(h)}" ${h === initCol ? "selected" : ""}>${escapeHtml(h)}</option>`
      ).join("");
      populateSingleSlotValueSelect(valId, initCol, initVal);
    });

    document.getElementById("customizeCardsModal").classList.add("open");
  });

  [
    { colId: "cardSlot1ColSelect", valId: "cardSlot1Select" },
    { colId: "cardSlot2ColSelect", valId: "cardSlot2Select" },
    { colId: "cardSlot3ColSelect", valId: "cardSlot3Select" }
  ].forEach(({ colId, valId }) => {
    document.getElementById(colId).addEventListener("change", (e) => {
      populateSingleSlotValueSelect(valId, e.target.value, "");
    });
  });

  document.getElementById("closeCustomizeModalBtn").addEventListener("click", () => {
    document.getElementById("customizeCardsModal").classList.remove("open");
  });
  document.getElementById("cancelCustomizeBtn").addEventListener("click", () => {
    document.getElementById("customizeCardsModal").classList.remove("open");
  });

  document.getElementById("resetCustomCardsBtn").addEventListener("click", () => {
    safeRemoveLocal(`GSHEET_CARD_CONFIGS_V2_${activeTabName || "default"}`);
    customCardConfigs = [];
    activeCardFilter = null;
    document.getElementById("customizeCardsModal").classList.remove("open");
    renderAnalytics();
    renderTable();
    showToast("รีเซ็ตการ์ดสรุปยอดเป็นค่าเริ่มต้นแล้ว");
  });

  document.getElementById("customizeCardsForm").addEventListener("submit", (e) => {
    e.preventDefault();
    customCardConfigs = [
      { col: document.getElementById("cardSlot1ColSelect").value, val: document.getElementById("cardSlot1Select").value },
      { col: document.getElementById("cardSlot2ColSelect").value, val: document.getElementById("cardSlot2Select").value },
      { col: document.getElementById("cardSlot3ColSelect").value, val: document.getElementById("cardSlot3Select").value }
    ];
    saveCustomCardConfigs(activeTabName || "default", customCardConfigs);
    activeCardFilter = null;
    currentPage = 1;
    document.getElementById("customizeCardsModal").classList.remove("open");
    renderAnalytics();
    renderTable();
    showToast("บันทึกการตั้งค่าคอลัมน์และค่าของทั้ง 3 การ์ดเรียบร้อยแล้ว");
  });

  // Modal เลือกคอลัมน์ที่ต้องการแสดงในตาราง
  let tempSelectedCols = new Set();

  const updateColPickerHint = () => {
    const hint = document.getElementById("colPickerCountHint");
    if (hint) {
      hint.textContent = `เลือกแสดง ${tempSelectedCols.size} จาก ${sheetHeaders.length} คอลัมน์ (ระบบจะจำค่าที่เลือกไว้ให้โดยอัตโนมัติ)`;
    }
  };

  const renderColPickerCheckboxes = (filterText = "") => {
    const grid = document.getElementById("colCheckboxGrid");
    if (!grid) return;
    grid.innerHTML = "";
    const q = filterText.toLowerCase().trim();

    sheetHeaders.forEach(col => {
      if (q && !col.toLowerCase().includes(q)) return;
      const isChecked = tempSelectedCols.has(col);
      const label = document.createElement("label");
      label.className = `col-check-item ${isChecked ? "checked" : ""}`;
      label.innerHTML = `
        <input type="checkbox" value="${escapeHtml(col)}" ${isChecked ? "checked" : ""}>
        <span class="col-check-name" title="${escapeHtml(col)}">${escapeHtml(col)}</span>
      `;
      const cb = label.querySelector("input");
      cb.addEventListener("change", () => {
        if (cb.checked) {
          tempSelectedCols.add(col);
          label.classList.add("checked");
        } else {
          tempSelectedCols.delete(col);
          label.classList.remove("checked");
        }
        updateColPickerHint();
      });
      grid.appendChild(label);
    });
    updateColPickerHint();
  };

  document.getElementById("selectTableColsBtn").addEventListener("click", () => {
    if (!isConnected || sheetHeaders.length === 0) return;
    tempSelectedCols = new Set(visibleTableHeaders.length > 0 ? visibleTableHeaders : sheetHeaders);
    document.getElementById("colPickerSearchInput").value = "";
    renderColPickerCheckboxes("");
    document.getElementById("columnPickerModal").classList.add("open");
  });

  document.getElementById("colPickerSearchInput").addEventListener("input", (e) => {
    renderColPickerCheckboxes(e.target.value);
  });

  document.getElementById("selectAllColsBtn").addEventListener("click", () => {
    sheetHeaders.forEach(h => tempSelectedCols.add(h));
    renderColPickerCheckboxes(document.getElementById("colPickerSearchInput").value);
  });

  document.getElementById("clearAllColsBtn").addEventListener("click", () => {
    tempSelectedCols.clear();
    renderColPickerCheckboxes(document.getElementById("colPickerSearchInput").value);
  });

  document.getElementById("closeColPickerBtn").addEventListener("click", () => {
    document.getElementById("columnPickerModal").classList.remove("open");
  });
  document.getElementById("cancelColPickerBtn").addEventListener("click", () => {
    document.getElementById("columnPickerModal").classList.remove("open");
  });

  document.getElementById("applyColPickerBtn").addEventListener("click", () => {
    if (tempSelectedCols.size === 0) {
      showToast("กรุณาเลือกอย่างน้อย 1 คอลัมน์เพื่อแสดงในตาราง");
      return;
    }
    // รักษาลำดับคอลัมน์ตามต้นฉบับใน Google Sheet
    visibleTableHeaders = sheetHeaders.filter(h => tempSelectedCols.has(h));
    saveVisibleHeaders(activeTabName || "default", visibleTableHeaders);
    document.getElementById("columnPickerModal").classList.remove("open");
    renderTable();
    showToast(`อัปเดตตารางให้แสดง ${visibleTableHeaders.length} คอลัมน์แล้ว`);
  });

  // Toggle Directory Collapse/Expand
  document.getElementById("toggleDirectoryBtn").addEventListener("click", () => {
    isDirectoryExpanded = !isDirectoryExpanded;
    safeSetLocal("CALIB_DIR_EXPANDED", String(isDirectoryExpanded));
    applyDirectoryCollapseUI();
  });

  // Role Toggle (Viewer Mode <-> Admin Mode)
  document.getElementById("adminToggleBtn").addEventListener("click", () => {
    if (isAdminMode) {
      sync2faStatusUI();
      document.getElementById("newAdminPinInput").value = "";
      document.getElementById("adminManageModal").classList.add("open");
    } else {
      document.getElementById("adminPinInput").value = "";
      document.getElementById("adminAuthModal").classList.add("open");
      setTimeout(() => document.getElementById("adminPinInput").focus(), 50);
    }
  });

  document.getElementById("closeAdminModalBtn").addEventListener("click", () => {
    document.getElementById("adminAuthModal").classList.remove("open");
  });
  document.getElementById("cancelAdminBtn").addEventListener("click", () => {
    document.getElementById("adminAuthModal").classList.remove("open");
  });

  document.getElementById("adminAuthForm").addEventListener("submit", (e) => {
    e.preventDefault();
    const entered = document.getElementById("adminPinInput").value.trim();
    if (entered === getStoredAdminPin()) {
      isAdminMode = true;
      safeSetSession("CALIB_IS_ADMIN", "true");
      document.getElementById("adminAuthModal").classList.remove("open");
      applyRoleUI();
      renderTable();
      showToast("เข้าสู่โหมด Admin เรียบร้อยแล้ว");
    } else {
      showToast("รหัสผ่าน Admin ไม่ถูกต้อง");
      document.getElementById("adminPinInput").value = "";
      document.getElementById("adminPinInput").focus();
    }
  });

  document.getElementById("closeAdminManageBtn").addEventListener("click", () => {
    document.getElementById("adminManageModal").classList.remove("open");
  });

  document.getElementById("logoutAdminBtn").addEventListener("click", () => {
    isAdminMode = false;
    safeRemoveSession("CALIB_IS_ADMIN");
    document.getElementById("adminManageModal").classList.remove("open");
    applyRoleUI();
    renderTable();
    showToast("ออกจากโหมด Admin แล้ว");
  });

  document.getElementById("changePinForm").addEventListener("submit", (e) => {
    e.preventDefault();
    const newPin = document.getElementById("newAdminPinInput").value.trim();
    if (newPin.length < 4) {
      showToast("กรุณากรอกรหัสผ่านใหม่อย่างน้อย 4 ตัวอักษร");
      return;
    }
    safeSetLocal("CALIB_ADMIN_PIN", newPin);
    document.getElementById("adminManageModal").classList.remove("open");
    showToast("บันทึกรหัสผ่าน Admin ใหม่เรียบร้อยแล้ว");
  });

  // Navigation Tabs (Overview | Data Table | Summary)
  const switchMainView = (view) => {
    activeNavView = view;
    document.querySelectorAll(".nav-tab").forEach(t => {
      t.classList.toggle("active", t.dataset.view === view);
    });

    const overviewEl = document.getElementById("viewOverview");
    const summaryEl = document.getElementById("viewSummary");

    if (view === "analytics") {
      if (overviewEl) overviewEl.style.display = "none";
      if (summaryEl) summaryEl.style.display = "flex";
      renderSummaryView();
      window.scrollTo({ top: 0, behavior: "smooth" });
    } else if (view === "jobs") {
      if (overviewEl) overviewEl.style.display = "flex";
      if (summaryEl) summaryEl.style.display = "none";
      if (!isDirectoryExpanded) {
        isDirectoryExpanded = true;
        safeSetLocal("CALIB_DIR_EXPANDED", "true");
        applyDirectoryCollapseUI();
      }
      document.getElementById("mainJobTableSection").scrollIntoView({ behavior: "smooth" });
    } else {
      if (overviewEl) overviewEl.style.display = "flex";
      if (summaryEl) summaryEl.style.display = "none";
      window.scrollTo({ top: 0, behavior: "smooth" });
    }
  };

  document.querySelectorAll(".nav-tab").forEach(tab => {
    tab.addEventListener("click", () => switchMainView(tab.dataset.view));
  });

  // Summary View Selectors & Export Summary CSV
  document.getElementById("sumPrimaryColSelect").addEventListener("change", (e) => {
    sumPrimaryCol = e.target.value;
    renderSummaryView();
  });
  document.getElementById("sumSecondaryColSelect").addEventListener("change", (e) => {
    sumSecondaryCol = e.target.value;
    renderSummaryView();
  });
  document.getElementById("sumDateColSelect").addEventListener("change", (e) => {
    sumDateCol = e.target.value;
    renderSummaryView();
  });

  document.getElementById("exportSummaryCsvBtn").addEventListener("click", () => {
    const scopedRows = getScopedRows();
    if (scopedRows.length === 0 || !sumPrimaryCol) return;
    const map = {};
    scopedRows.forEach(r => {
      const v = String(r[sumPrimaryCol] ?? "").trim() || "(ว่าง)";
      map[v] = (map[v] || 0) + 1;
    });
    const sorted = Object.entries(map).sort((a, b) => b[1] - a[1]);
    const lines = [
      `"Rank","${sumPrimaryCol.replace(/"/g, '""')}","Count","Percentage"`,
      ...sorted.map(([val, cnt], idx) => `"${idx + 1}","${val.replace(/"/g, '""')}","${cnt}","${((cnt / scopedRows.length) * 100).toFixed(2)}%"`)
    ];
    const blob = new Blob(["\uFEFF" + lines.join("\n")], { type: "text/csv;charset=utf-8;" });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `Summary_${sumPrimaryCol}_${activeTabName || "Sheet"}.csv`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
    showToast(`ส่งออกรายงานสรุปยอด "${sumPrimaryCol}" เป็นไฟล์ CSV แล้ว`);
  });

  document.getElementById("jumpToAllJobsBtn").addEventListener("click", () => {
    if (!isDirectoryExpanded) {
      isDirectoryExpanded = true;
      safeSetLocal("CALIB_DIR_EXPANDED", "true");
      applyDirectoryCollapseUI();
    }
    activeCardFilter = null;
    selectedSecondaryValue = "ALL";
    renderAnalytics();
    renderTable();
    document.getElementById("mainJobTableSection").scrollIntoView({ behavior: "smooth" });
  });

  document.getElementById("viewAllPlanBtn").addEventListener("click", () => {
    document.getElementById("mainJobTableSection").scrollIntoView({ behavior: "smooth" });
  });

  // Modals Backdrop & Escape
  document.querySelectorAll(".modal-backdrop").forEach(backdrop => {
    backdrop.addEventListener("click", (e) => {
      if (e.target === backdrop) backdrop.classList.remove("open");
    });
  });
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape") {
      document.querySelectorAll(".modal-backdrop.open").forEach(m => m.classList.remove("open"));
    }
  });

  // Row 1..N Cutoff Control (เช่น กรอก 5000 = โชว์ Row 1 ถึง 5000 และเมื่อมีแถวแทรกเข้ามาเป็น 5001 จะขยับให้เห็น 5001 แต่ซ่อนแถวหลังจากนั้น)
  const rowLimitInput = document.getElementById("rowLimitInput");
  const clearRowLimitBtn = document.getElementById("clearRowLimitBtn");

  rowLimitInput.addEventListener("input", (e) => {
    const val = parseInt(e.target.value, 10);
    rowCutoffLimit = (!isNaN(val) && val > 0) ? val : 0;
    if (rowCutoffLimit > 0) {
      rowCutoffBaselineFilled = rowsData.filter(isSubstantiveDataRow).length;
      safeSetLocal("GSHEET_ROW_CUTOFF", String(rowCutoffLimit));
      safeSetLocal("GSHEET_ROW_CUTOFF_BASELINE_FILLED", String(rowCutoffBaselineFilled));
    } else {
      rowCutoffBaselineFilled = 0;
      safeRemoveLocal("GSHEET_ROW_CUTOFF");
      safeRemoveLocal("GSHEET_ROW_CUTOFF_BASELINE_FILLED");
    }
    currentPage = 1;
    renderAnalytics();
    renderTable();
  });

  document.getElementById("hideTemplateBlanksCheck").addEventListener("change", (e) => {
    hideTemplateBlanks = e.target.checked;
    safeSetLocal("GSHEET_HIDE_TEMPLATE_BLANKS", String(hideTemplateBlanks));
    currentPage = 1;
    renderAnalytics();
    renderTable();
  });

  clearRowLimitBtn.addEventListener("click", () => {
    rowCutoffLimit = 0;
    rowCutoffBaselineFilled = 0;
    safeRemoveLocal("GSHEET_ROW_CUTOFF");
    safeRemoveLocal("GSHEET_ROW_CUTOFF_BASELINE_FILLED");
    currentPage = 1;
    renderAnalytics();
    renderTable();
    showToast("ยกเลิกการจำกัดเลข Row แล้ว");
  });

  // Search & Filter
  const searchInput = document.getElementById("searchInput");
  const clearSearchBtn = document.getElementById("clearSearchBtn");
  searchInput.addEventListener("input", (e) => {
    currentSearch = e.target.value;
    currentPage = 1;
    clearSearchBtn.style.display = currentSearch ? "block" : "none";
    renderAnalytics();
    renderTable();
  });

  clearSearchBtn.addEventListener("click", () => {
    currentSearch = "";
    currentPage = 1;
    searchInput.value = "";
    clearSearchBtn.style.display = "none";
    renderAnalytics();
    renderTable();
  });

  document.getElementById("dynamicColFilterSelect").addEventListener("change", (e) => {
    const chosenVal = e.target.value;
    if (chosenVal === "ALL") {
      activeCardFilter = null;
    } else {
      const targetCol = (activeCardFilter && activeCardFilter.col) ? activeCardFilter.col : selectedGroupCol;
      activeCardFilter = { col: targetCol, val: chosenVal };
    }
    currentPage = 1;
    renderAnalytics();
    renderTable();
  });

  // Pagination Navigation Buttons (First / Prev / Next / Last)
  const goToPage = (targetPage) => {
    const filtered = getFilteredAndSortedRows();
    const totalPages = Math.max(1, Math.ceil(filtered.length / ROWS_PER_PAGE));
    currentPage = Math.min(totalPages, Math.max(1, targetPage));
    renderTable();
    document.getElementById("mainJobTableSection").scrollIntoView({ behavior: "smooth" });
  };

  document.getElementById("firstPageBtn").addEventListener("click", () => goToPage(1));
  document.getElementById("prevPageBtn").addEventListener("click", () => goToPage(currentPage - 1));
  document.getElementById("nextPageBtn").addEventListener("click", () => goToPage(currentPage + 1));
  document.getElementById("lastPageBtn").addEventListener("click", () => {
    const filtered = getFilteredAndSortedRows();
    const totalPages = Math.max(1, Math.ceil(filtered.length / ROWS_PER_PAGE));
    goToPage(totalPages);
  });

  // 2-Way Synchronized Top & Bottom Horizontal Scrollbars for Table
  const topScrollEl = document.getElementById("topTableScroll");
  const mainScrollEl = document.getElementById("mainTableScroll");
  let isSyncingScroll = false;

  if (topScrollEl && mainScrollEl) {
    topScrollEl.addEventListener("scroll", () => {
      if (isSyncingScroll) return;
      isSyncingScroll = true;
      mainScrollEl.scrollLeft = topScrollEl.scrollLeft;
      requestAnimationFrame(() => { isSyncingScroll = false; });
    });

    mainScrollEl.addEventListener("scroll", () => {
      if (isSyncingScroll) return;
      isSyncingScroll = true;
      topScrollEl.scrollLeft = mainScrollEl.scrollLeft;
      requestAnimationFrame(() => { isSyncingScroll = false; });
    });

    document.getElementById("slideTableLeftBtn").addEventListener("click", () => {
      mainScrollEl.scrollBy({ left: -320, behavior: "smooth" });
    });

    document.getElementById("slideTableRightBtn").addEventListener("click", () => {
      mainScrollEl.scrollBy({ left: 320, behavior: "smooth" });
    });

    window.addEventListener("resize", syncTopTableSlider);
  }

  document.getElementById("resetFilterBtn").addEventListener("click", () => {
    activeCardFilter = null;
    selectedSecondaryValue = "ALL";
    currentSearch = "";
    sortState = { column: "", direction: "asc" };
    currentPage = 1;
    searchInput.value = "";
    clearSearchBtn.style.display = "none";
    renderAnalytics();
    renderTable();
    showToast("รีเซ็ตตัวกรองทั้งหมดแล้ว");
  });

  // Action Buttons
  document.getElementById("refreshNowBtn").addEventListener("click", () => fetchFromSheet(true));
  document.getElementById("overviewSyncBtn").addEventListener("click", () => fetchFromSheet(true));
  document.getElementById("openAddJobBtn").addEventListener("click", () => openDynamicRowModal(null));
  document.getElementById("overviewAddBtn").addEventListener("click", () => openDynamicRowModal(null));
  document.getElementById("overviewExportBtn").addEventListener("click", exportFilteredToCSV);
  document.getElementById("tableExportCsvBtn").addEventListener("click", exportFilteredToCSV);

  document.getElementById("openModalBtn").addEventListener("click", () => {
    document.getElementById("apiUrlInput").value = connectionSource;
    document.getElementById("optionalTabInput").value = activeTabName;
    document.getElementById("apiModal").classList.add("open");
  });

  document.getElementById("closeModalBtn").addEventListener("click", () => {
    document.getElementById("apiModal").classList.remove("open");
  });

  document.getElementById("saveApiBtn").addEventListener("click", () => {
    const rawUrl = document.getElementById("apiUrlInput").value.trim();
    const tabName = document.getElementById("optionalTabInput").value.trim();
    const parsed = parseConnectionTarget(rawUrl, tabName);

    if (parsed.mode === "none" || parsed.mode === "invalid") {
      showToast("กรุณาวางลิงก์ Google Sheet (https://docs.google.com/spreadsheets/d/...) หรือ Apps Script Web App URL");
      return;
    }

    connectionSource = rawUrl;
    activeTabName = tabName;
    selectedGroupCol = "";
    activeCardFilter = null;
    selectedSecondaryCol = "";
    selectedSecondaryValue = "ALL";

    safeSetLocal("GSHEET_SOURCE_INPUT", connectionSource);
    safeSetLocal("GSHEET_TAB_NAME", activeTabName);
    document.getElementById("apiModal").classList.remove("open");

    if (pollTimer) clearInterval(pollTimer);
    fetchFromSheet(true);
    pollTimer = setInterval(() => fetchFromSheet(false), 10000);
  });

  document.getElementById("disconnectApiBtn").addEventListener("click", () => {
    connectionSource = "";
    activeTabName = "";
    connectionMode = "none";
    isConnected = false;
    sheetHeaders = [];
    rowsData = [];
    availableTabs = [];
    safeRemoveLocal("GSHEET_SOURCE_INPUT");
    safeRemoveLocal("GSHEET_TAB_NAME");
    safeRemoveLocal("GSHEET_API_URL");
    if (pollTimer) clearInterval(pollTimer);

    document.getElementById("brandSheetTitle").textContent = "TMC Calibration";
    document.getElementById("directoryTitle").textContent = "Sheet data directory";
    document.getElementById("apiModal").classList.remove("open");
    updateTabSelectorUI();
    updateConnectionState("Not connected", "offline");
    renderAnalytics();
    renderTable();
    showToast("ยกเลิกการเชื่อมต่อและล้างข้อมูลแล้ว");
  });

  // Dynamic Row Form Submit (Add or Edit)
  document.getElementById("closeJobModalBtn").addEventListener("click", () => {
    document.getElementById("jobFormModal").classList.remove("open");
  });
  document.getElementById("cancelJobBtn").addEventListener("click", () => {
    document.getElementById("jobFormModal").classList.remove("open");
  });

  document.getElementById("jobForm").addEventListener("submit", async (e) => {
    e.preventDefault();
    const payload = {};
    sheetHeaders.forEach((col, idx) => {
      const inp = document.getElementById(`dynField_${idx}`);
      payload[col] = inp ? inp.value.trim() : "";
    });

    document.getElementById("jobFormModal").classList.remove("open");

    if (editingRowObj) {
      payload._rowIndex = editingRowObj._rowIndex;
      Object.assign(editingRowObj, payload);
      renderAnalytics();
      renderTable();
      await syncChangeToSheet("updateRow", payload);
    } else {
      rowsData.push(payload);
      renderAnalytics();
      renderTable();
      await syncChangeToSheet("addRow", payload);
    }
  });

  // Delete Row Confirm
  document.getElementById("closeDeleteModalBtn").addEventListener("click", () => {
    document.getElementById("deleteConfirmModal").classList.remove("open");
  });
  document.getElementById("cancelDeleteBtn").addEventListener("click", () => {
    document.getElementById("deleteConfirmModal").classList.remove("open");
  });
  document.getElementById("confirmDeleteBtn").addEventListener("click", async () => {
    if (!pendingDeleteRowObj) return;
    const targetRow = pendingDeleteRowObj;
    pendingDeleteRowObj = null;
    document.getElementById("deleteConfirmModal").classList.remove("open");
    rowsData = rowsData.filter(r => r._rowIndex !== targetRow._rowIndex);
    renderAnalytics();
    renderTable();
    await syncChangeToSheet("deleteRow", { _rowIndex: targetRow._rowIndex });
  });
});
