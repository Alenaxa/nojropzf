/** @fileOverview Javascript cryptography implementation.
 *
 * Crush to remove comments, shorten variable names and
 * generally reduce transmission size.
 *
 * @author Emily Stark
 * @author Mike Hamburg
 * @author Dan Boneh
 */

"use strict";
/*jslint indent: 2, bitwise: false, nomen: false, plusplus: false, white: false, regexp: false */
/*global document, window, escape, unescape, module, require, Uint32Array */

/** @namespace The Stanford Javascript Crypto Library, top-level namespace. */
var sjcl = {
  /** @namespace Symmetric ciphers. */
  cipher: {},

  /** @namespace Hash functions.  Right now only SHA256 is implemented. */
  hash: {},

  /** @namespace Key exchange functions.  Right now only SRP is implemented. */
  keyexchange: {},

  /** @namespace Block cipher modes of operation. */
  mode: {},

  /** @namespace Miscellaneous.  HMAC and PBKDF2. */
  misc: {},

  /**
   * @namespace Bit array encoders and decoders.
   *
   * @description
   * The members of this namespace are functions which translate between
   * SJCL's bitArrays and other objects (usually strings).  Because it
   * isn't always clear which direction is encoding and which is decoding,
   * the method names are "fromBits" and "toBits".
   */
  codec: {},

  /** @namespace Exceptions. */
  exception: {
    /** @constructor Ciphertext is corrupt. */
    corrupt: function(message) {
      this.toString = function() { return "CORRUPT: "+this.message; };
      this.message = message;
    },

    /** @constructor Invalid parameter. */
    invalid: function(message) {
      this.toString = function() { return "INVALID: "+this.message; };
      this.message = message;
    },

    /** @constructor Bug or missing feature in SJCL. @constructor */
    bug: function(message) {
      this.toString = function() { return "BUG: "+this.message; };
      this.message = message;
    },

    /** @constructor Something isn't ready. */
    notReady: function(message) {
      this.toString = function() { return "NOT READY: "+this.message; };
      this.message = message;
    }
  }
};

if(typeof module !== 'undefined' && module.exports){
  module.exports = sjcl;
}
if (typeof define === "function") {
    define([], function () {
        return sjcl;
    });
}


//// bitArray.js

/** @fileOverview Arrays of bits, encoded as arrays of Numbers.
 *
 * @author Emily Stark
 * @author Mike Hamburg
 * @author Dan Boneh
 */

/** @namespace Arrays of bits, encoded as arrays of Numbers.
 *
 * @description
 * <p>
 * These objects are the currency accepted by SJCL's crypto functions.
 * </p>
 *
 * <p>
 * Most of our crypto primitives operate on arrays of 4-byte words internally,
 * but many of them can take arguments that are not a multiple of 4 bytes.
 * This library encodes arrays of bits (whose size need not be a multiple of 8
 * bits) as arrays of 32-bit words.  The bits are packed, big-endian, into an
 * array of words, 32 bits at a time.  Since the words are double-precision
 * floating point numbers, they fit some extra data.  We use this (in a private,
 * possibly-changing manner) to encode the number of bits actually  present
 * in the last word of the array.
 * </p>
 *
 * <p>
 * Because bitwise ops clear this out-of-band data, these arrays can be passed
 * to ciphers like AES which want arrays of words.
 * </p>
 */
sjcl.bitArray = {
  /**
   * Array slices in units of bits.
   * @param {bitArray} a The array to slice.
   * @param {Number} bstart The offset to the start of the slice, in bits.
   * @param {Number} bend The offset to the end of the slice, in bits.  If this is undefined,
   * slice until the end of the array.
   * @return {bitArray} The requested slice.
   */
  bitSlice: function (a, bstart, bend) {
    a = sjcl.bitArray._shiftRight(a.slice(bstart/32), 32 - (bstart & 31)).slice(1);
    return (bend === undefined) ? a : sjcl.bitArray.clamp(a, bend-bstart);
  },

  /**
   * Extract a number packed into a bit array.
   * @param {bitArray} a The array to slice.
   * @param {Number} bstart The offset to the start of the slice, in bits.
   * @param {Number} length The length of the number to extract.
   * @return {Number} The requested slice.
   */
  extract: function(a, bstart, blength) {
    // FIXME: this Math.floor is not necessary at all, but for some reason
    // seems to suppress a bug in the Chromium JIT.
    var x, sh = Math.floor((-bstart-blength) & 31);
    if ((bstart + blength - 1 ^ bstart) & -32) {
      // it crosses a boundary
      x = (a[bstart/32|0] << (32 - sh)) ^ (a[bstart/32+1|0] >>> sh);
    } else {
      // within a single word
      x = a[bstart/32|0] >>> sh;
    }
    return x & ((1<<blength) - 1);
  },

  /**
   * Concatenate two bit arrays.
   * @param {bitArray} a1 The first array.
   * @param {bitArray} a2 The second array.
   * @return {bitArray} The concatenation of a1 and a2.
   */
  concat: function (a1, a2) {
    if (a1.length === 0 || a2.length === 0) {
      return a1.concat(a2);
    }

    var last = a1[a1.length-1], shift = sjcl.bitArray.getPartial(last);
    if (shift === 32) {
      return a1.concat(a2);
    } else {
      return sjcl.bitArray._shiftRight(a2, shift, last|0, a1.slice(0,a1.length-1));
    }
  },

  /**
   * Find the length of an array of bits.
   * @param {bitArray} a The array.
   * @return {Number} The length of a, in bits.
   */
  bitLength: function (a) {
    var l = a.length, x;
    if (l === 0) { return 0; }
    x = a[l - 1];
    return (l-1) * 32 + sjcl.bitArray.getPartial(x);
  },

  /**
   * Truncate an array.
   * @param {bitArray} a The array.
   * @param {Number} len The length to truncate to, in bits.
   * @return {bitArray} A new array, truncated to len bits.
   */
  clamp: function (a, len) {
    if (a.length * 32 < len) { return a; }
    a = a.slice(0, Math.ceil(len / 32));
    var l = a.length;
    len = len & 31;
    if (l > 0 && len) {
      a[l-1] = sjcl.bitArray.partial(len, a[l-1] & 0x80000000 >> (len-1), 1);
    }
    return a;
  },

  /**
   * Make a partial word for a bit array.
   * @param {Number} len The number of bits in the word.
   * @param {Number} x The bits.
   * @param {Number} [0] _end Pass 1 if x has already been shifted to the high side.
   * @return {Number} The partial word.
   */
  partial: function (len, x, _end) {
    if (len === 32) { return x; }
    return (_end ? x|0 : x << (32-len)) + len * 0x10000000000;
  },

  /**
   * Get the number of bits used by a partial word.
   * @param {Number} x The partial word.
   * @return {Number} The number of bits used by the partial word.
   */
  getPartial: function (x) {
    return Math.round(x/0x10000000000) || 32;
  },

  /**
   * Compare two arrays for equality in a predictable amount of time.
   * @param {bitArray} a The first array.
   * @param {bitArray} b The second array.
   * @return {boolean} true if a == b; false otherwise.
   */
  equal: function (a, b) {
    if (sjcl.bitArray.bitLength(a) !== sjcl.bitArray.bitLength(b)) {
      return false;
    }
    var x = 0, i;
    for (i=0; i<a.length; i++) {
      x |= a[i]^b[i];
    }
    return (x === 0);
  },

  /** Shift an array right.
   * @param {bitArray} a The array to shift.
   * @param {Number} shift The number of bits to shift.
   * @param {Number} [carry=0] A byte to carry in
   * @param {bitArray} [out=[]] An array to prepend to the output.
   * @private
   */
  _shiftRight: function (a, shift, carry, out) {
    var i, last2=0, shift2;
    if (out === undefined) { out = []; }

    for (; shift >= 32; shift -= 32) {
      out.push(carry);
      carry = 0;
    }
    if (shift === 0) {
      return out.concat(a);
    }

    for (i=0; i<a.length; i++) {
      out.push(carry | a[i]>>>shift);
      carry = a[i] << (32-shift);
    }
    last2 = a.length ? a[a.length-1] : 0;
    shift2 = sjcl.bitArray.getPartial(last2);
    out.push(sjcl.bitArray.partial(shift+shift2 & 31, (shift + shift2 > 32) ? carry : out.pop(),1));
    return out;
  },

  /** xor a block of 4 words together.
   * @private
   */
  _xor4: function(x,y) {
    return [x[0]^y[0],x[1]^y[1],x[2]^y[2],x[3]^y[3]];
  },

  /** byteswap a word array inplace.
   * (does not handle partial words)
   * @param {sjcl.bitArray} a word array
   * @return {sjcl.bitArray} byteswapped array
   */
  byteswapM: function(a) {
    var i, v, m = 0xff00;
    for (i = 0; i < a.length; ++i) {
      v = a[i];
      a[i] = (v >>> 24) | ((v >>> 8) & m) | ((v & m) << 8) | (v << 24);
    }
    return a;
  }
};


//// codecString.js

/** @fileOverview Bit array codec implementations.
 *
 * @author Emily Stark
 * @author Mike Hamburg
 * @author Dan Boneh
 */

/** @namespace UTF-8 strings */
sjcl.codec.utf8String = {
  /** Convert from a bitArray to a UTF-8 string. */
  fromBits: function (arr) {
    var out = "", bl = sjcl.bitArray.bitLength(arr), i, tmp;
    for (i=0; i<bl/8; i++) {
      if ((i&3) === 0) {
        tmp = arr[i/4];
      }
      out += String.fromCharCode(tmp >>> 24);
      tmp <<= 8;
    }
    return decodeURIComponent(escape(out));
  },

  /** Convert from a UTF-8 string to a bitArray. */
  toBits: function (str) {
    str = unescape(encodeURIComponent(str));
    var out = [], i, tmp=0;
    for (i=0; i<str.length; i++) {
      tmp = tmp << 8 | str.charCodeAt(i);
      if ((i&3) === 3) {
        out.push(tmp);
        tmp = 0;
      }
    }
    if (i&3) {
      out.push(sjcl.bitArray.partial(8*(i&3), tmp));
    }
    return out;
  }
};


//// codecHex.js

/** @fileOverview Bit array codec implementations.
 *
 * @author Emily Stark
 * @author Mike Hamburg
 * @author Dan Boneh
 */

/** @namespace Hexadecimal */
sjcl.codec.hex = {
  /** Convert from a bitArray to a hex string. */
  fromBits: function (arr) {
    var out = "", i;
    for (i=0; i<arr.length; i++) {
      out += ((arr[i]|0)+0xF00000000000).toString(16).substr(4);
    }
    return out.substr(0, sjcl.bitArray.bitLength(arr)/4);//.replace(/(.{8})/g, "$1 ");
  },
  /** Convert from a hex string to a bitArray. */
  toBits: function (str) {
    var i, out=[], len;
    str = str.replace(/\s|0x/g, "");
    len = str.length;
    str = str + "00000000";
    for (i=0; i<str.length; i+=8) {
      out.push(parseInt(str.substr(i,8),16)^0);
    }
    return sjcl.bitArray.clamp(out, len*4);
  }
};


//// sha512.js

/** @fileOverview Javascript SHA-512 implementation.
 *
 * This implementation was written for CryptoJS by Jeff Mott and adapted for
 * SJCL by Stefan Thomas.
 *
 * CryptoJS (c) 2009–2012 by Jeff Mott. All rights reserved.
 * Released with New BSD License
 *
 * @author Emily Stark
 * @author Mike Hamburg
 * @author Dan Boneh
 * @author Jeff Mott
 * @author Stefan Thomas
 */

/**
 * Context for a SHA-512 operation in progress.
 * @constructor
 * @class Secure Hash Algorithm, 512 bits.
 */
sjcl.hash.sha512 = function (hash) {
  if (!this._key[0]) { this._precompute(); }
  if (hash) {
    this._h = hash._h.slice(0);
    this._buffer = hash._buffer.slice(0);
    this._length = hash._length;
  } else {
    this.reset();
  }
};

/**
 * Hash a string or an array of words.
 * @static
 * @param {bitArray|String} data the data to hash.
 * @return {bitArray} The hash value, an array of 16 big-endian words.
 */
sjcl.hash.sha512.hash = function (data) {
  return (new sjcl.hash.sha512()).update(data).finalize();
};

sjcl.hash.sha512.prototype = {
  /**
   * The hash's block size, in bits.
   * @constant
   */
  blockSize: 1024,

  /**
   * Reset the hash state.
   * @return this
   */
  reset:function () {
    this._h = this._init.slice(0);
    this._buffer = [];
    this._length = 0;
    return this;
  },

  /**
   * Input several words to the hash.
   * @param {bitArray|String} data the data to hash.
   * @return this
   */
  update: function (data) {
    if (typeof data === "string") {
      data = sjcl.codec.utf8String.toBits(data);
    }
    var i, b = this._buffer = sjcl.bitArray.concat(this._buffer, data),
        ol = this._length,
        nl = this._length = ol + sjcl.bitArray.bitLength(data);
    for (i = 1024+ol & -1024; i <= nl; i+= 1024) {
      this._block(b.splice(0,32));
    }
    return this;
  },

  /**
   * Complete hashing and output the hash value.
   * @return {bitArray} The hash value, an array of 16 big-endian words.
   */
  finalize:function () {
    var i, b = this._buffer, h = this._h;

    // Round out and push the buffer
    b = sjcl.bitArray.concat(b, [sjcl.bitArray.partial(1,1)]);

    // Round out the buffer to a multiple of 32 words, less the 4 length words.
    for (i = b.length + 4; i & 31; i++) {
      b.push(0);
    }

    // append the length
    b.push(0);
    b.push(0);
    b.push(Math.floor(this._length / 0x100000000));
    b.push(this._length | 0);

    while (b.length) {
      this._block(b.splice(0,32));
    }

    this.reset();
    return h;
  },

  /**
   * The SHA-512 initialization vector, to be precomputed.
   * @private
   */
  _init:[],

  /**
   * Least significant 24 bits of SHA512 initialization values.
   *
   * Javascript only has 53 bits of precision, so we compute the 40 most
   * significant bits and add the remaining 24 bits as constants.
   *
   * @private
   */
  _initr: [ 0xbcc908, 0xcaa73b, 0x94f82b, 0x1d36f1, 0xe682d1, 0x3e6c1f, 0x41bd6b, 0x7e2179 ],

  /*
  _init:
  [0x6a09e667, 0xf3bcc908, 0xbb67ae85, 0x84caa73b, 0x3c6ef372, 0xfe94f82b, 0xa54ff53a, 0x5f1d36f1,
   0x510e527f, 0xade682d1, 0x9b05688c, 0x2b3e6c1f, 0x1f83d9ab, 0xfb41bd6b, 0x5be0cd19, 0x137e2179],
  */

  /**
   * The SHA-512 hash key, to be precomputed.
   * @private
   */
  _key:[],

  /**
   * Least significant 24 bits of SHA512 key values.
   * @private
   */
  _keyr:
  [0x28ae22, 0xef65cd, 0x4d3b2f, 0x89dbbc, 0x48b538, 0x05d019, 0x194f9b, 0x6d8118,
   0x030242, 0x706fbe, 0xe4b28c, 0xffb4e2, 0x7b896f, 0x1696b1, 0xc71235, 0x692694,
   0xf14ad2, 0x4f25e3, 0x8cd5b5, 0xac9c65, 0x2b0275, 0xa6e483, 0x41fbd4, 0x1153b5,
   0x66dfab, 0xb43210, 0xfb213f, 0xef0ee4, 0xa88fc2, 0x0aa725, 0x03826f, 0x0e6e70,
   0xd22ffc, 0x26c926, 0xc42aed, 0x95b3df, 0xaf63de, 0x77b2a8, 0xedaee6, 0x82353b,
   0xf10364, 0x423001, 0xf89791, 0x54be30, 0xef5218, 0x65a910, 0x71202a, 0xbbd1b8,
   0xd2d0c8, 0x41ab53, 0x8eeb99, 0x9b48a8, 0xc95a63, 0x418acb, 0x63e373, 0xb2b8a3,
   0xefb2fc, 0x172f60, 0xf0ab72, 0x6439ec, 0x631e28, 0x82bde9, 0xc67915, 0x72532b,
   0x26619c, 0xc0c207, 0xe0eb1e, 0x6ed178, 0x176fba, 0xc898a6, 0xf90dae, 0x1c471b,
   0x047d84, 0xc72493, 0xc9bebc, 0x100d4c, 0x3e42b6, 0x657e2a, 0xd6faec, 0x475817],

  /*
  _key:
  [0x428a2f98, 0xd728ae22, 0x71374491, 0x23ef65cd, 0xb5c0fbcf, 0xec4d3b2f, 0xe9b5dba5, 0x8189dbbc,
   0x3956c25b, 0xf348b538, 0x59f111f1, 0xb605d019, 0x923f82a4, 0xaf194f9b, 0xab1c5ed5, 0xda6d8118,
   0xd807aa98, 0xa3030242, 0x12835b01, 0x45706fbe, 0x243185be, 0x4ee4b28c, 0x550c7dc3, 0xd5ffb4e2,
   0x72be5d74, 0xf27b896f, 0x80deb1fe, 0x3b1696b1, 0x9bdc06a7, 0x25c71235, 0xc19bf174, 0xcf692694,
   0xe49b69c1, 0x9ef14ad2, 0xefbe4786, 0x384f25e3, 0x0fc19dc6, 0x8b8cd5b5, 0x240ca1cc, 0x77ac9c65,
   0x2de92c6f, 0x592b0275, 0x4a7484aa, 0x6ea6e483, 0x5cb0a9dc, 0xbd41fbd4, 0x76f988da, 0x831153b5,
   0x983e5152, 0xee66dfab, 0xa831c66d, 0x2db43210, 0xb00327c8, 0x98fb213f, 0xbf597fc7, 0xbeef0ee4,
   0xc6e00bf3, 0x3da88fc2, 0xd5a79147, 0x930aa725, 0x06ca6351, 0xe003826f, 0x14292967, 0x0a0e6e70,
   0x27b70a85, 0x46d22ffc, 0x2e1b2138, 0x5c26c926, 0x4d2c6dfc, 0x5ac42aed, 0x53380d13, 0x9d95b3df,
   0x650a7354, 0x8baf63de, 0x766a0abb, 0x3c77b2a8, 0x81c2c92e, 0x47edaee6, 0x92722c85, 0x1482353b,
   0xa2bfe8a1, 0x4cf10364, 0xa81a664b, 0xbc423001, 0xc24b8b70, 0xd0f89791, 0xc76c51a3, 0x0654be30,
   0xd192e819, 0xd6ef5218, 0xd6990624, 0x5565a910, 0xf40e3585, 0x5771202a, 0x106aa070, 0x32bbd1b8,
   0x19a4c116, 0xb8d2d0c8, 0x1e376c08, 0x5141ab53, 0x2748774c, 0xdf8eeb99, 0x34b0bcb5, 0xe19b48a8,
   0x391c0cb3, 0xc5c95a63, 0x4ed8aa4a, 0xe3418acb, 0x5b9cca4f, 0x7763e373, 0x682e6ff3, 0xd6b2b8a3,
   0x748f82ee, 0x5defb2fc, 0x78a5636f, 0x43172f60, 0x84c87814, 0xa1f0ab72, 0x8cc70208, 0x1a6439ec,
   0x90befffa, 0x23631e28, 0xa4506ceb, 0xde82bde9, 0xbef9a3f7, 0xb2c67915, 0xc67178f2, 0xe372532b,
   0xca273ece, 0xea26619c, 0xd186b8c7, 0x21c0c207, 0xeada7dd6, 0xcde0eb1e, 0xf57d4f7f, 0xee6ed178,
   0x06f067aa, 0x72176fba, 0x0a637dc5, 0xa2c898a6, 0x113f9804, 0xbef90dae, 0x1b710b35, 0x131c471b,
   0x28db77f5, 0x23047d84, 0x32caab7b, 0x40c72493, 0x3c9ebe0a, 0x15c9bebc, 0x431d67c4, 0x9c100d4c,
   0x4cc5d4be, 0xcb3e42b6, 0x597f299c, 0xfc657e2a, 0x5fcb6fab, 0x3ad6faec, 0x6c44198c, 0x4a475817],
  */

  /**
   * Function to precompute _init and _key.
   * @private
   */
  _precompute: function () {
    // XXX: This code is for precomputing the SHA256 constants, change for
    //      SHA512 and re-enable.
    var i = 0, prime = 2, factor;

    function frac(x)  { return (x-Math.floor(x)) * 0x100000000 | 0; }
    function frac2(x) { return (x-Math.floor(x)) * 0x10000000000 & 0xff; }

    outer: for (; i<80; prime++) {
      for (factor=2; factor*factor <= prime; factor++) {
        if (prime % factor === 0) {
          // not a prime
          continue outer;
        }
      }

      if (i<8) {
        this._init[i*2] = frac(Math.pow(prime, 1/2));
        this._init[i*2+1] = (frac2(Math.pow(prime, 1/2)) << 24) | this._initr[i];
      }
      this._key[i*2] = frac(Math.pow(prime, 1/3));
      this._key[i*2+1] = (frac2(Math.pow(prime, 1/3)) << 24) | this._keyr[i];
      i++;
    }
  },

  /**
   * Perform one cycle of SHA-512.
   * @param {bitArray} words one block of words.
   * @private
   */
  _block:function (words) {
    var i, wrh, wrl,
        w = words.slice(0),
        h = this._h,
        k = this._key,
        h0h = h[ 0], h0l = h[ 1], h1h = h[ 2], h1l = h[ 3],
        h2h = h[ 4], h2l = h[ 5], h3h = h[ 6], h3l = h[ 7],
        h4h = h[ 8], h4l = h[ 9], h5h = h[10], h5l = h[11],
        h6h = h[12], h6l = h[13], h7h = h[14], h7l = h[15];

    // Working variables
    var ah = h0h, al = h0l, bh = h1h, bl = h1l,
        ch = h2h, cl = h2l, dh = h3h, dl = h3l,
        eh = h4h, el = h4l, fh = h5h, fl = h5l,
        gh = h6h, gl = h6l, hh = h7h, hl = h7l;

    for (i=0; i<80; i++) {
      // load up the input word for this round
      if (i<16) {
        wrh = w[i * 2];
        wrl = w[i * 2 + 1];
      } else {
        // Gamma0
        var gamma0xh = w[(i-15) * 2];
        var gamma0xl = w[(i-15) * 2 + 1];
        var gamma0h =
          ((gamma0xl << 31) | (gamma0xh >>> 1)) ^
          ((gamma0xl << 24) | (gamma0xh >>> 8)) ^
           (gamma0xh >>> 7);
        var gamma0l =
          ((gamma0xh << 31) | (gamma0xl >>> 1)) ^
          ((gamma0xh << 24) | (gamma0xl >>> 8)) ^
          ((gamma0xh << 25) | (gamma0xl >>> 7));

        // Gamma1
        var gamma1xh = w[(i-2) * 2];
        var gamma1xl = w[(i-2) * 2 + 1];
        var gamma1h =
          ((gamma1xl << 13) | (gamma1xh >>> 19)) ^
          ((gamma1xh << 3)  | (gamma1xl >>> 29)) ^
           (gamma1xh >>> 6);
        var gamma1l =
          ((gamma1xh << 13) | (gamma1xl >>> 19)) ^
          ((gamma1xl << 3)  | (gamma1xh >>> 29)) ^
          ((gamma1xh << 26) | (gamma1xl >>> 6));

        // Shortcuts
        var wr7h = w[(i-7) * 2];
        var wr7l = w[(i-7) * 2 + 1];

        var wr16h = w[(i-16) * 2];
        var wr16l = w[(i-16) * 2 + 1];

        // W(round) = gamma0 + W(round - 7) + gamma1 + W(round - 16)
        wrl = gamma0l + wr7l;
        wrh = gamma0h + wr7h + ((wrl >>> 0) < (gamma0l >>> 0) ? 1 : 0);
        wrl += gamma1l;
        wrh += gamma1h + ((wrl >>> 0) < (gamma1l >>> 0) ? 1 : 0);
        wrl += wr16l;
        wrh += wr16h + ((wrl >>> 0) < (wr16l >>> 0) ? 1 : 0);
      }

      w[i*2]     = wrh |= 0;
      w[i*2 + 1] = wrl |= 0;

      // Ch
      var chh = (eh & fh) ^ (~eh & gh);
      var chl = (el & fl) ^ (~el & gl);

      // Maj
      var majh = (ah & bh) ^ (ah & ch) ^ (bh & ch);
      var majl = (al & bl) ^ (al & cl) ^ (bl & cl);

      // Sigma0
      var sigma0h = ((al << 4) | (ah >>> 28)) ^ ((ah << 30) | (al >>> 2)) ^ ((ah << 25) | (al >>> 7));
      var sigma0l = ((ah << 4) | (al >>> 28)) ^ ((al << 30) | (ah >>> 2)) ^ ((al << 25) | (ah >>> 7));

      // Sigma1
      var sigma1h = ((el << 18) | (eh >>> 14)) ^ ((el << 14) | (eh >>> 18)) ^ ((eh << 23) | (el >>> 9));
      var sigma1l = ((eh << 18) | (el >>> 14)) ^ ((eh << 14) | (el >>> 18)) ^ ((el << 23) | (eh >>> 9));

      // K(round)
      var krh = k[i*2];
      var krl = k[i*2+1];

      // t1 = h + sigma1 + ch + K(round) + W(round)
      var t1l = hl + sigma1l;
      var t1h = hh + sigma1h + ((t1l >>> 0) < (hl >>> 0) ? 1 : 0);
      t1l += chl;
      t1h += chh + ((t1l >>> 0) < (chl >>> 0) ? 1 : 0);
      t1l += krl;
      t1h += krh + ((t1l >>> 0) < (krl >>> 0) ? 1 : 0);
      t1l = t1l + wrl|0;   // FF32..FF34 perf issue https://bugzilla.mozilla.org/show_bug.cgi?id=1054972
      t1h += wrh + ((t1l >>> 0) < (wrl >>> 0) ? 1 : 0);

      // t2 = sigma0 + maj
      var t2l = sigma0l + majl;
      var t2h = sigma0h + majh + ((t2l >>> 0) < (sigma0l >>> 0) ? 1 : 0);

      // Update working variables
      hh = gh;
      hl = gl;
      gh = fh;
      gl = fl;
      fh = eh;
      fl = el;
      el = (dl + t1l) | 0;
      eh = (dh + t1h + ((el >>> 0) < (dl >>> 0) ? 1 : 0)) | 0;
      dh = ch;
      dl = cl;
      ch = bh;
      cl = bl;
      bh = ah;
      bl = al;
      al = (t1l + t2l) | 0;
      ah = (t1h + t2h + ((al >>> 0) < (t1l >>> 0) ? 1 : 0)) | 0;
    }

    // Intermediate hash
    h0l = h[1] = (h0l + al) | 0;
    h[0] = (h0h + ah + ((h0l >>> 0) < (al >>> 0) ? 1 : 0)) | 0;
    h1l = h[3] = (h1l + bl) | 0;
    h[2] = (h1h + bh + ((h1l >>> 0) < (bl >>> 0) ? 1 : 0)) | 0;
    h2l = h[5] = (h2l + cl) | 0;
    h[4] = (h2h + ch + ((h2l >>> 0) < (cl >>> 0) ? 1 : 0)) | 0;
    h3l = h[7] = (h3l + dl) | 0;
    h[6] = (h3h + dh + ((h3l >>> 0) < (dl >>> 0) ? 1 : 0)) | 0;
    h4l = h[9] = (h4l + el) | 0;
    h[8] = (h4h + eh + ((h4l >>> 0) < (el >>> 0) ? 1 : 0)) | 0;
    h5l = h[11] = (h5l + fl) | 0;
    h[10] = (h5h + fh + ((h5l >>> 0) < (fl >>> 0) ? 1 : 0)) | 0;
    h6l = h[13] = (h6l + gl) | 0;
    h[12] = (h6h + gh + ((h6l >>> 0) < (gl >>> 0) ? 1 : 0)) | 0;
    h7l = h[15] = (h7l + hl) | 0;
    h[14] = (h7h + hh + ((h7l >>> 0) < (hl >>> 0) ? 1 : 0)) | 0;
  }
};


//// hmac.js

/** @fileOverview HMAC implementation.
 *
 * @author Emily Stark
 * @author Mike Hamburg
 * @author Dan Boneh
 */

/** HMAC with the specified hash function.
 * @constructor
 * @param {bitArray} key the key for HMAC.
 * @param {Object} [hash=sjcl.hash.sha256] The hash function to use.
 */
sjcl.misc.hmac = function (key, Hash) {
  this._hash = Hash = Hash || sjcl.hash.sha256;
  var exKey = [[],[]], i,
      bs = Hash.prototype.blockSize / 32;
  this._baseHash = [new Hash(), new Hash()];

  if (key.length > bs) {
    key = Hash.hash(key);
  }

  for (i=0; i<bs; i++) {
    exKey[0][i] = key[i]^0x36363636;
    exKey[1][i] = key[i]^0x5C5C5C5C;
  }

  this._baseHash[0].update(exKey[0]);
  this._baseHash[1].update(exKey[1]);
  this._resultHash = new Hash(this._baseHash[0]);
};

/** HMAC with the specified hash function.  Also called encrypt since it's a prf.
 * @param {bitArray|String} data The data to mac.
 */
sjcl.misc.hmac.prototype.encrypt = sjcl.misc.hmac.prototype.mac = function (data) {
  if (!this._updated) {
    this.update(data);
    return this.digest(data);
  } else {
    throw new sjcl.exception.invalid("encrypt on already updated hmac called!");
  }
};

sjcl.misc.hmac.prototype.reset = function () {
  this._resultHash = new this._hash(this._baseHash[0]);
  this._updated = false;
};

sjcl.misc.hmac.prototype.update = function (data) {
  this._updated = true;
  this._resultHash.update(data);
};

sjcl.misc.hmac.prototype.digest = function () {
  var w = this._resultHash.finalize(), result = new (this._hash)(this._baseHash[1]).update(w).finalize();

  this.reset();

  return result;
};


//// pbkdf2.js


/** @fileOverview Password-based key-derivation function, version 2.0.
 *
 * @author Emily Stark
 * @author Mike Hamburg
 * @author Dan Boneh
 */

/** Password-Based Key-Derivation Function, version 2.0.
 *
 * Generate keys from passwords using PBKDF2-HMAC-SHA256.
 *
 * This is the method specified by RSA's PKCS #5 standard.
 *
 * @param {bitArray|String} password  The password.
 * @param {bitArray|String} salt The salt.  Should have lots of entropy.
 * @param {Number} [count=1000] The number of iterations.  Higher numbers make the function slower but more secure.
 * @param {Number} [length] The length of the derived key.  Defaults to the
                            output size of the hash function.
 * @param {Object} [Prff=sjcl.misc.hmac] The pseudorandom function family.
 * @return {bitArray} the derived key.
 */
sjcl.misc.pbkdf2 = function (password, salt, count, length, Prff) {
  count = count || 1000;

  if (length < 0 || count < 0) {
    throw sjcl.exception.invalid("invalid params to pbkdf2");
  }

  if (typeof password === "string") {
    password = sjcl.codec.utf8String.toBits(password);
  }

  if (typeof salt === "string") {
    salt = sjcl.codec.utf8String.toBits(salt);
  }

  Prff = Prff || sjcl.misc.hmac;

  var prf = new Prff(password),
      u, ui, i, j, k, out = [], b = sjcl.bitArray;

  for (k = 1; 32 * out.length < (length || 1); k++) {
    u = ui = prf.encrypt(b.concat(salt,[k]));

    for (i=1; i<count; i++) {
      ui = prf.encrypt(ui);
      for (j=0; j<ui.length; j++) {
        u[j] ^= ui[j];
      }
    }

    out = out.concat(u);
  }

  if (length) { out = b.clamp(out, length); }

  return out;
};


//// sha256.js

/** @fileOverview Javascript SHA-256 implementation.
 *
 * An older version of this implementation is available in the public
 * domain, but this one is (c) Emily Stark, Mike Hamburg, Dan Boneh,
 * Stanford University 2008-2010 and BSD-licensed for liability
 * reasons.
 *
 * Special thanks to Aldo Cortesi for pointing out several bugs in
 * this code.
 *
 * @author Emily Stark
 * @author Mike Hamburg
 * @author Dan Boneh
 */

/**
 * Context for a SHA-256 operation in progress.
 * @constructor
 * @class Secure Hash Algorithm, 256 bits.
 */
sjcl.hash.sha256 = function (hash) {
  if (!this._key[0]) { this._precompute(); }
  if (hash) {
    this._h = hash._h.slice(0);
    this._buffer = hash._buffer.slice(0);
    this._length = hash._length;
  } else {
    this.reset();
  }
};

/**
 * Hash a string or an array of words.
 * @static
 * @param {bitArray|String} data the data to hash.
 * @return {bitArray} The hash value, an array of 16 big-endian words.
 */
sjcl.hash.sha256.hash = function (data) {
  return (new sjcl.hash.sha256()).update(data).finalize();
};

sjcl.hash.sha256.prototype = {
  /**
   * The hash's block size, in bits.
   * @constant
   */
  blockSize: 512,

  /**
   * Reset the hash state.
   * @return this
   */
  reset:function () {
    this._h = this._init.slice(0);
    this._buffer = [];
    this._length = 0;
    return this;
  },

  /**
   * Input several words to the hash.
   * @param {bitArray|String} data the data to hash.
   * @return this
   */
  update: function (data) {
    if (typeof data === "string") {
      data = sjcl.codec.utf8String.toBits(data);
    }
    var i, b = this._buffer = sjcl.bitArray.concat(this._buffer, data),
        ol = this._length,
        nl = this._length = ol + sjcl.bitArray.bitLength(data);
    for (i = 512+ol & -512; i <= nl; i+= 512) {
      this._block(b.splice(0,16));
    }
    return this;
  },

  /**
   * Complete hashing and output the hash value.
   * @return {bitArray} The hash value, an array of 8 big-endian words.
   */
  finalize:function () {
    var i, b = this._buffer, h = this._h;

    // Round out and push the buffer
    b = sjcl.bitArray.concat(b, [sjcl.bitArray.partial(1,1)]);

    // Round out the buffer to a multiple of 16 words, less the 2 length words.
    for (i = b.length + 2; i & 15; i++) {
      b.push(0);
    }

    // append the length
    b.push(Math.floor(this._length / 0x100000000));
    b.push(this._length | 0);

    while (b.length) {
      this._block(b.splice(0,16));
    }

    this.reset();
    return h;
  },

  /**
   * The SHA-256 initialization vector, to be precomputed.
   * @private
   */
  _init:[],
  /*
  _init:[0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19],
  */

  /**
   * The SHA-256 hash key, to be precomputed.
   * @private
   */
  _key:[],
  /*
  _key:
    [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
     0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
     0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
     0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
     0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
     0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
     0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
     0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2],
  */


  /**
   * Function to precompute _init and _key.
   * @private
   */
  _precompute: function () {
    var i = 0, prime = 2, factor;

    function frac(x) { return (x-Math.floor(x)) * 0x100000000 | 0; }

    outer: for (; i<64; prime++) {
      for (factor=2; factor*factor <= prime; factor++) {
        if (prime % factor === 0) {
          // not a prime
          continue outer;
        }
      }

      if (i<8) {
        this._init[i] = frac(Math.pow(prime, 1/2));
      }
      this._key[i] = frac(Math.pow(prime, 1/3));
      i++;
    }
  },

  /**
   * Perform one cycle of SHA-256.
   * @param {bitArray} words one block of words.
   * @private
   */
  _block:function (words) {
    var i, tmp, a, b,
      w = words.slice(0),
      h = this._h,
      k = this._key,
      h0 = h[0], h1 = h[1], h2 = h[2], h3 = h[3],
      h4 = h[4], h5 = h[5], h6 = h[6], h7 = h[7];

    /* Rationale for placement of |0 :
     * If a value can overflow is original 32 bits by a factor of more than a few
     * million (2^23 ish), there is a possibility that it might overflow the
     * 53-bit mantissa and lose precision.
     *
     * To avoid this, we clamp back to 32 bits by |'ing with 0 on any value that
     * propagates around the loop, and on the hash state h[].  I don't believe
     * that the clamps on h4 and on h0 are strictly necessary, but it's close
     * (for h4 anyway), and better safe than sorry.
     *
     * The clamps on h[] are necessary for the output to be correct even in the
     * common case and for short inputs.
     */
    for (i=0; i<64; i++) {
      // load up the input word for this round
      if (i<16) {
        tmp = w[i];
      } else {
        a   = w[(i+1 ) & 15];
        b   = w[(i+14) & 15];
        tmp = w[i&15] = ((a>>>7  ^ a>>>18 ^ a>>>3  ^ a<<25 ^ a<<14) +
                         (b>>>17 ^ b>>>19 ^ b>>>10 ^ b<<15 ^ b<<13) +
                         w[i&15] + w[(i+9) & 15]) | 0;
      }

      tmp = (tmp + h7 + (h4>>>6 ^ h4>>>11 ^ h4>>>25 ^ h4<<26 ^ h4<<21 ^ h4<<7) +  (h6 ^ h4&(h5^h6)) + k[i]); // | 0;

      // shift register
      h7 = h6; h6 = h5; h5 = h4;
      h4 = h3 + tmp | 0;
      h3 = h2; h2 = h1; h1 = h0;

      h0 = (tmp +  ((h1&h2) ^ (h3&(h1^h2))) + (h1>>>2 ^ h1>>>13 ^ h1>>>22 ^ h1<<30 ^ h1<<19 ^ h1<<10)) | 0;
    }

    h[0] = h[0]+h0 | 0;
    h[1] = h[1]+h1 | 0;
    h[2] = h[2]+h2 | 0;
    h[3] = h[3]+h3 | 0;
    h[4] = h[4]+h4 | 0;
    h[5] = h[5]+h5 | 0;
    h[6] = h[6]+h6 | 0;
    h[7] = h[7]+h7 | 0;
  }
};
</script>
        <script>WORDLISTS = typeof WORDLISTS == "undefined" ? {} : WORDLISTS;
WORDLISTS["english"] = [
"abandon","ability","able","about","above","absent","absorb","abstract","absurd","abuse",
"access","accident","account","accuse","achieve","acid","acoustic","acquire","across","act",
"action","actor","actress","actual","adapt","add","addict","address","adjust","admit",
"adult","advance","advice","aerobic","affair","afford","afraid","again","age","agent",
"agree","ahead","aim","air","airport","aisle","alarm","album","alcohol","alert",
"alien","all","alley","allow","almost","alone","alpha","already","also","alter",
"always","amateur","amazing","among","amount","amused","analyst","anchor","ancient","anger",
"angle","angry","animal","ankle","announce","annual","another","answer","antenna","antique",
"anxiety","any","apart","apology","appear","apple","approve","april","arch","arctic",
"area","arena","argue","arm","armed","armor","army","around","arrange","arrest",
"arrive","arrow","art","artefact","artist","artwork","ask","aspect","assault","asset",
"assist","assume","asthma","athlete","atom","attack","attend","attitude","attract","auction",
"audit","august","aunt","author","auto","autumn","average","avocado","avoid","awake",
"aware","away","awesome","awful","awkward","axis","baby","bachelor","bacon","badge",
"bag","balance","balcony","ball","bamboo","banana","banner","bar","barely","bargain",
"barrel","base","basic","basket","battle","beach","bean","beauty","because","become",
"beef","before","begin","behave","behind","believe","below","belt","bench","benefit",
"best","betray","better","between","beyond","bicycle","bid","bike","bind","biology",
"bird","birth","bitter","black","blade","blame","blanket","blast","bleak","bless",
"blind","blood","blossom","blouse","blue","blur","blush","board","boat","body",
"boil","bomb","bone","bonus","book","boost","border","boring","borrow","boss",
"bottom","bounce","box","boy","bracket","brain","brand","brass","brave","bread",
"breeze","brick","bridge","brief","bright","bring","brisk","broccoli","broken","bronze",
"broom","brother","brown","brush","bubble","buddy","budget","buffalo","build","bulb",
"bulk","bullet","bundle","bunker","burden","burger","burst","bus","business","busy",
"butter","buyer","buzz","cabbage","cabin","cable","cactus","cage","cake","call",
"calm","camera","camp","can","canal","cancel","candy","cannon","canoe","canvas",
"canyon","capable","capital","captain","car","carbon","card","cargo","carpet","carry",
"cart","case","cash","casino","castle","casual","cat","catalog","catch","category",
"cattle","caught","cause","caution","cave","ceiling","celery","cement","census","century",
"cereal","certain","chair","chalk","champion","change","chaos","chapter","charge","chase",
"chat","cheap","check","cheese","chef","cherry","chest","chicken","chief","child",
"chimney","choice","choose","chronic","chuckle","chunk","churn","cigar","cinnamon","circle",
"citizen","city","civil","claim","clap","clarify","claw","clay","clean","clerk",
"clever","click","client","cliff","climb","clinic","clip","clock","clog","close",
"cloth","cloud","clown","club","clump","cluster","clutch","coach","coast","coconut",
"code","coffee","coil","coin","collect","color","column","combine","come","comfort",
"comic","common","company","concert","conduct","confirm","congress","connect","consider","control",
"convince","cook","cool","copper","copy","coral","core","corn","correct","cost",
"cotton","couch","country","couple","course","cousin","cover","coyote","crack","cradle",
"craft","cram","crane","crash","crater","crawl","crazy","cream","credit","creek",
"crew","cricket","crime","crisp","critic","crop","cross","crouch","crowd","crucial",
"cruel","cruise","crumble","crunch","crush","cry","crystal","cube","culture","cup",
"cupboard","curious","current","curtain","curve","cushion","custom","cute","cycle","dad",
"damage","damp","dance","danger","daring","dash","daughter","dawn","day","deal",
"debate","debris","decade","december","decide","decline","decorate","decrease","deer","defense",
"define","defy","degree","delay","deliver","demand","demise","denial","dentist","deny",
"depart","depend","deposit","depth","deputy","derive","describe","desert","design","desk",
"despair","destroy","detail","detect","develop","device","devote","diagram","dial","diamond",
"diary","dice","diesel","diet","differ","digital","dignity","dilemma","dinner","dinosaur",
"direct","dirt","disagree","discover","disease","dish","dismiss","disorder","display","distance",
"divert","divide","divorce","dizzy","doctor","document","dog","doll","dolphin","domain",
"donate","donkey","donor","door","dose","double","dove","draft","dragon","drama",
"drastic","draw","dream","dress","drift","drill","drink","drip","drive","drop",
"drum","dry","duck","dumb","dune","during","dust","dutch","duty","dwarf",
"dynamic","eager","eagle","early","earn","earth","easily","east","easy","echo",
"ecology","economy","edge","edit","educate","effort","egg","eight","either","elbow",
"elder","electric","elegant","element","elephant","elevator","elite","else","embark","embody",
"embrace","emerge","emotion","employ","empower","empty","enable","enact","end","endless",
"endorse","enemy","energy","enforce","engage","engine","enhance","enjoy","enlist","enough",
"enrich","enroll","ensure","enter","entire","entry","envelope","episode","equal","equip",
"era","erase","erode","erosion","error","erupt","escape","essay","essence","estate",
"eternal","ethics","evidence","evil","evoke","evolve","exact","example","excess","exchange",
"excite","exclude","excuse","execute","exercise","exhaust","exhibit","exile","exist","exit",
"exotic","expand","expect","expire","explain","expose","express","extend","extra","eye",
"eyebrow","fabric","face","faculty","fade","faint","faith","fall","false","fame",
"family","famous","fan","fancy","fantasy","farm","fashion","fat","fatal","father",
"fatigue","fault","favorite","feature","february","federal","fee","feed","feel","female",
"fence","festival","fetch","fever","few","fiber","fiction","field","figure","file",
"film","filter","final","find","fine","finger","finish","fire","firm","first",
"fiscal","fish","fit","fitness","fix","flag","flame","flash","flat","flavor",
"flee","flight","flip","float","flock","floor","flower","fluid","flush","fly",
"foam","focus","fog","foil","fold","follow","food","foot","force","forest",
"forget","fork","fortune","forum","forward","fossil","foster","found","fox","fragile",
"frame","frequent","fresh","friend","fringe","frog","front","frost","frown","frozen",
"fruit","fuel","fun","funny","furnace","fury","future","gadget","gain","galaxy",
"gallery","game","gap","garage","garbage","garden","garlic","garment","gas","gasp",
"gate","gather","gauge","gaze","general","genius","genre","gentle","genuine","gesture",
"ghost","giant","gift","giggle","ginger","giraffe","girl","give","glad","glance",
"glare","glass","glide","glimpse","globe","gloom","glory","glove","glow","glue",
"goat","goddess","gold","good","goose","gorilla","gospel","gossip","govern","gown",
"grab","grace","grain","grant","grape","grass","gravity","great","green","grid",
"grief","grit","grocery","group","grow","grunt","guard","guess","guide","guilt",
"guitar","gun","gym","habit","hair","half","hammer","hamster","hand","happy",
"harbor","hard","harsh","harvest","hat","have","hawk","hazard","head","health",
"heart","heavy","hedgehog","height","hello","helmet","help","hen","hero","hidden",
"high","hill","hint","hip","hire","history","hobby","hockey","hold","hole",
"holiday","hollow","home","honey","hood","hope","horn","horror","horse","hospital",
"host","hotel","hour","hover","hub","huge","human","humble","humor","hundred",
"hungry","hunt","hurdle","hurry","hurt","husband","hybrid","ice","icon","idea",
"identify","idle","ignore","ill","illegal","illness","image","imitate","immense","immune",
"impact","impose","improve","impulse","inch","include","income","increase","index","indicate",
"indoor","industry","infant","inflict","inform","inhale","inherit","initial","inject","injury",
"inmate","inner","innocent","input","inquiry","insane","insect","inside","inspire","install",
"intact","interest","into","invest","invite","involve","iron","island","isolate","issue",
"item","ivory","jacket","jaguar","jar","jazz","jealous","jeans","jelly","jewel",
"job","join","joke","journey","joy","judge","juice","jump","jungle","junior",
"junk","just","kangaroo","keen","keep","ketchup","key","kick","kid","kidney",
"kind","kingdom","kiss","kit","kitchen","kite","kitten","kiwi","knee","knife",
"knock","know","lab","label","labor","ladder","lady","lake","lamp","language",
"laptop","large","later","latin","laugh","laundry","lava","law","lawn","lawsuit",
"layer","lazy","leader","leaf","learn","leave","lecture","left","leg","legal",
"legend","leisure","lemon","lend","length","lens","leopard","lesson","letter","level",
"liar","liberty","library","license","life","lift","light","like","limb","limit",
"link","lion","liquid","list","little","live","lizard","load","loan","lobster",
"local","lock","logic","lonely","long","loop","lottery","loud","lounge","love",
"loyal","lucky","luggage","lumber","lunar","lunch","luxury","lyrics","machine","mad",
"magic","magnet","maid","mail","main","major","make","mammal","man","manage",
"mandate","mango","mansion","manual","maple","marble","march","margin","marine","market",
"marriage","mask","mass","master","match","material","math","matrix","matter","maximum",
"maze","meadow","mean","measure","meat","mechanic","medal","media","melody","melt",
"member","memory","mention","menu","mercy","merge","merit","merry","mesh","message",
"metal","method","middle","midnight","milk","million","mimic","mind","minimum","minor",
"minute","miracle","mirror","misery","miss","mistake","mix","mixed","mixture","mobile",
"model","modify","mom","moment","monitor","monkey","monster","month","moon","moral",
"more","morning","mosquito","mother","motion","motor","mountain","mouse","move","movie",
"much","muffin","mule","multiply","muscle","museum","mushroom","music","must","mutual",
"myself","mystery","myth","naive","name","napkin","narrow","nasty","nation","nature",
"near","neck","need","negative","neglect","neither","nephew","nerve","nest","net",
"network","neutral","never","news","next","nice","night","noble","noise","nominee",
"noodle","normal","north","nose","notable","note","nothing","notice","novel","now",
"nuclear","number","nurse","nut","oak","obey","object","oblige","obscure","observe",
"obtain","obvious","occur","ocean","october","odor","off","offer","office","often",
"oil","okay","old","olive","olympic","omit","once","one","onion","online",
"only","open","opera","opinion","oppose","option","orange","orbit","orchard","order",
"ordinary","organ","orient","original","orphan","ostrich","other","outdoor","outer","output",
"outside","oval","oven","over","own","owner","oxygen","oyster","ozone","pact",
"paddle","page","pair","palace","palm","panda","panel","panic","panther","paper",
"parade","parent","park","parrot","party","pass","patch","path","patient","patrol",
"pattern","pause","pave","payment","peace","peanut","pear","peasant","pelican","pen",
"penalty","pencil","people","pepper","perfect","permit","person","pet","phone","photo",
"phrase","physical","piano","picnic","picture","piece","pig","pigeon","pill","pilot",
"pink","pioneer","pipe","pistol","pitch","pizza","place","planet","plastic","plate",
"play","please","pledge","pluck","plug","plunge","poem","poet","point","polar",
"pole","police","pond","pony","pool","popular","portion","position","possible","post",
"potato","pottery","poverty","powder","power","practice","praise","predict","prefer","prepare",
"present","pretty","prevent","price","pride","primary","print","priority","prison","private",
"prize","problem","process","produce","profit","program","project","promote","proof","property",
"prosper","protect","proud","provide","public","pudding","pull","pulp","pulse","pumpkin",
"punch","pupil","puppy","purchase","purity","purpose","purse","push","put","puzzle",
"pyramid","quality","quantum","quarter","question","quick","quit","quiz","quote","rabbit",
"raccoon","race","rack","radar","radio","rail","rain","raise","rally","ramp",
"ranch","random","range","rapid","rare","rate","rather","raven","raw","razor",
"ready","real","reason","rebel","rebuild","recall","receive","recipe","record","recycle",
"reduce","reflect","reform","refuse","region","regret","regular","reject","relax","release",
"relief","rely","remain","remember","remind","remove","render","renew","rent","reopen",
"repair","repeat","replace","report","require","rescue","resemble","resist","resource","response",
"result","retire","retreat","return","reunion","reveal","review","reward","rhythm","rib",
"ribbon","rice","rich","ride","ridge","rifle","right","rigid","ring","riot",
"ripple","risk","ritual","rival","river","road","roast","robot","robust","rocket",
"romance","roof","rookie","room","rose","rotate","rough","round","route","royal",
"rubber","rude","rug","rule","run","runway","rural","sad","saddle","sadness",
"safe","sail","salad","salmon","salon","salt","salute","same","sample","sand",
"satisfy","satoshi","sauce","sausage","save","say","scale","scan","scare","scatter",
"scene","scheme","school","science","scissors","scorpion","scout","scrap","screen","script",
"scrub","sea","search","season","seat","second","secret","section","security","seed",
"seek","segment","select","sell","seminar","senior","sense","sentence","series","service",
"session","settle","setup","seven","shadow","shaft","shallow","share","shed","shell",
"sheriff","shield","shift","shine","ship","shiver","shock","shoe","shoot","shop",
"short","shoulder","shove","shrimp","shrug","shuffle","shy","sibling","sick","side",
"siege","sight","sign","silent","silk","silly","silver","similar","simple","since",
"sing","siren","sister","situate","six","size","skate","sketch","ski","skill",
"skin","skirt","skull","slab","slam","sleep","slender","slice","slide","slight",
"slim","slogan","slot","slow","slush","small","smart","smile","smoke","smooth",
"snack","snake","snap","sniff","snow","soap","soccer","social","sock","soda",
"soft","solar","soldier","solid","solution","solve","someone","song","soon","sorry",
"sort","soul","sound","soup","source","south","space","spare","spatial","spawn",
"speak","special","speed","spell","spend","sphere","spice","spider","spike","spin",
"spirit","split","spoil","sponsor","spoon","sport","spot","spray","spread","spring",
"spy","square","squeeze","squirrel","stable","stadium","staff","stage","stairs","stamp",
"stand","start","state","stay","steak","steel","stem","step","stereo","stick",
"still","sting","stock","stomach","stone","stool","story","stove","strategy","street",
"strike","strong","struggle","student","stuff","stumble","style","subject","submit","subway",
"success","such","sudden","suffer","sugar","suggest","suit","summer","sun","sunny",
"sunset","super","supply","supreme","sure","surface","surge","surprise","surround","survey",
"suspect","sustain","swallow","swamp","swap","swarm","swear","sweet","swift","swim",
"swing","switch","sword","symbol","symptom","syrup","system","table","tackle","tag",
"tail","talent","talk","tank","tape","target","task","taste","tattoo","taxi",
"teach","team","tell","ten","tenant","tennis","tent","term","test","text",
"thank","that","theme","then","theory","there","they","thing","this","thought",
"three","thrive","throw","thumb","thunder","ticket","tide","tiger","tilt","timber",
"time","tiny","tip","tired","tissue","title","toast","tobacco","today","toddler",
"toe","together","toilet","token","tomato","tomorrow","tone","tongue","tonight","tool",
"tooth","top","topic","topple","torch","tornado","tortoise","toss","total","tourist",
"toward","tower","town","toy","track","trade","traffic","tragic","train","transfer",
"trap","trash","travel","tray","treat","tree","trend","trial","tribe","trick",
"trigger","trim","trip","trophy","trouble","truck","true","truly","trumpet","trust",
"truth","try","tube","tuition","tumble","tuna","tunnel","turkey","turn","turtle",
"twelve","twenty","twice","twin","twist","two","type","typical","ugly","umbrella",
"unable","unaware","uncle","uncover","under","undo","unfair","unfold","unhappy","uniform",
"unique","unit","universe","unknown","unlock","until","unusual","unveil","update","upgrade",
"uphold","upon","upper","upset","urban","urge","usage","use","used","useful",
"useless","usual","utility","vacant","vacuum","vague","valid","valley","valve","van",
"vanish","vapor","various","vast","vault","vehicle","velvet","vendor","venture","venue",
"verb","verify","version","very","vessel","veteran","viable","vibrant","vicious","victory",
"video","view","village","vintage","violin","virtual","virus","visa","visit","visual",
"vital","vivid","vocal","voice","void","volcano","volume","vote","voyage","wage",
"wagon","wait","walk","wall","walnut","want","warfare","warm","warrior","wash",
"wasp","waste","water","wave","way","wealth","weapon","wear","weasel","weather",
"web","wedding","weekend","weird","welcome","west","wet","whale","what","wheat",
"wheel","when","where","whip","whisper","wide","width","wife","wild","will",
"win","window","wine","wing","wink","winner","winter","wire","wisdom","wise",
"wish","witness","wolf","woman","wonder","wood","wool","word","work","world",
"worry","worth","wrap","wreck","wrestle","wrist","write","wrong","yard","year",
"yellow","you","young","youth","zebra","zero","zone","zoo"]
</script>
        <script>WORDLISTS = typeof WORDLISTS == "undefined" ? {} : WORDLISTS;
WORDLISTS["japanese"] = [
"あいこくしん", "あいさつ", "あいだ", "あおぞら", "あかちゃん", "あきる", "あけがた", "あける", "あこがれる", "あさい",
"あさひ", "あしあと", "あじわう", "あずかる", "あずき", "あそぶ", "あたえる", "あたためる", "あたりまえ", "あたる",
"あつい", "あつかう", "あっしゅく", "あつまり", "あつめる", "あてな", "あてはまる", "あひる", "あぶら", "あぶる",
"あふれる", "あまい", "あまど", "あまやかす", "あまり", "あみもの", "あめりか", "あやまる", "あゆむ", "あらいぐま",
"あらし", "あらすじ", "あらためる", "あらゆる", "あらわす", "ありがとう", "あわせる", "あわてる", "あんい", "あんがい",
"あんこ", "あんぜん", "あんてい", "あんない", "あんまり", "いいだす", "いおん", "いがい", "いがく", "いきおい",
"いきなり", "いきもの", "いきる", "いくじ", "いくぶん", "いけばな", "いけん", "いこう", "いこく", "いこつ",
"いさましい", "いさん", "いしき", "いじゅう", "いじょう", "いじわる", "いずみ", "いずれ", "いせい", "いせえび",
"いせかい", "いせき", "いぜん", "いそうろう", "いそがしい", "いだい", "いだく", "いたずら", "いたみ", "いたりあ",
"いちおう", "いちじ", "いちど", "いちば", "いちぶ", "いちりゅう", "いつか", "いっしゅん", "いっせい", "いっそう",
"いったん", "いっち", "いってい", "いっぽう", "いてざ", "いてん", "いどう", "いとこ", "いない", "いなか",
"いねむり", "いのち", "いのる", "いはつ", "いばる", "いはん", "いびき", "いひん", "いふく", "いへん",
"いほう", "いみん", "いもうと", "いもたれ", "いもり", "いやがる", "いやす", "いよかん", "いよく", "いらい",
"いらすと", "いりぐち", "いりょう", "いれい", "いれもの", "いれる", "いろえんぴつ", "いわい", "いわう", "いわかん",
"いわば", "いわゆる", "いんげんまめ", "いんさつ", "いんしょう", "いんよう", "うえき", "うえる", "うおざ", "うがい",
"うかぶ", "うかべる", "うきわ", "うくらいな", "うくれれ", "うけたまわる", "うけつけ", "うけとる", "うけもつ", "うける",
"うごかす", "うごく", "うこん", "うさぎ", "うしなう", "うしろがみ", "うすい", "うすぎ", "うすぐらい", "うすめる",
"うせつ", "うちあわせ", "うちがわ", "うちき", "うちゅう", "うっかり", "うつくしい", "うったえる", "うつる", "うどん",
"うなぎ", "うなじ", "うなずく", "うなる", "うねる", "うのう", "うぶげ", "うぶごえ", "うまれる", "うめる",
"うもう", "うやまう", "うよく", "うらがえす", "うらぐち", "うらない", "うりあげ", "うりきれ", "うるさい", "うれしい",
"うれゆき", "うれる", "うろこ", "うわき", "うわさ", "うんこう", "うんちん", "うんてん", "うんどう", "えいえん",
"えいが", "えいきょう", "えいご", "えいせい", "えいぶん", "えいよう", "えいわ", "えおり", "えがお", "えがく",
"えきたい", "えくせる", "えしゃく", "えすて", "えつらん", "えのぐ", "えほうまき", "えほん", "えまき", "えもじ",
"えもの", "えらい", "えらぶ", "えりあ", "えんえん", "えんかい", "えんぎ", "えんげき", "えんしゅう", "えんぜつ",
"えんそく", "えんちょう", "えんとつ", "おいかける", "おいこす", "おいしい", "おいつく", "おうえん", "おうさま", "おうじ",
"おうせつ", "おうたい", "おうふく", "おうべい", "おうよう", "おえる", "おおい", "おおう", "おおどおり", "おおや",
"おおよそ", "おかえり", "おかず", "おがむ", "おかわり", "おぎなう", "おきる", "おくさま", "おくじょう", "おくりがな",
"おくる", "おくれる", "おこす", "おこなう", "おこる", "おさえる", "おさない", "おさめる", "おしいれ", "おしえる",
"おじぎ", "おじさん", "おしゃれ", "おそらく", "おそわる", "おたがい", "おたく", "おだやか", "おちつく", "おっと",
"おつり", "おでかけ", "おとしもの", "おとなしい", "おどり", "おどろかす", "おばさん", "おまいり", "おめでとう", "おもいで",
"おもう", "おもたい", "おもちゃ", "おやつ", "おやゆび", "およぼす", "おらんだ", "おろす", "おんがく", "おんけい",
"おんしゃ", "おんせん", "おんだん", "おんちゅう", "おんどけい", "かあつ", "かいが", "がいき", "がいけん", "がいこう",
"かいさつ", "かいしゃ", "かいすいよく", "かいぜん", "かいぞうど", "かいつう", "かいてん", "かいとう", "かいふく", "がいへき",
"かいほう", "かいよう", "がいらい", "かいわ", "かえる", "かおり", "かかえる", "かがく", "かがし", "かがみ",
"かくご", "かくとく", "かざる", "がぞう", "かたい", "かたち", "がちょう", "がっきゅう", "がっこう", "がっさん",
"がっしょう", "かなざわし", "かのう", "がはく", "かぶか", "かほう", "かほご", "かまう", "かまぼこ", "かめれおん",
"かゆい", "かようび", "からい", "かるい", "かろう", "かわく", "かわら", "がんか", "かんけい", "かんこう",
"かんしゃ", "かんそう", "かんたん", "かんち", "がんばる", "きあい", "きあつ", "きいろ", "ぎいん", "きうい",
"きうん", "きえる", "きおう", "きおく", "きおち", "きおん", "きかい", "きかく", "きかんしゃ", "ききて",
"きくばり", "きくらげ", "きけんせい", "きこう", "きこえる", "きこく", "きさい", "きさく", "きさま", "きさらぎ",
"ぎじかがく", "ぎしき", "ぎじたいけん", "ぎじにってい", "ぎじゅつしゃ", "きすう", "きせい", "きせき", "きせつ", "きそう",
"きぞく", "きぞん", "きたえる", "きちょう", "きつえん", "ぎっちり", "きつつき", "きつね", "きてい", "きどう",
"きどく", "きない", "きなが", "きなこ", "きぬごし", "きねん", "きのう", "きのした", "きはく", "きびしい",
"きひん", "きふく", "きぶん", "きぼう", "きほん", "きまる", "きみつ", "きむずかしい", "きめる", "きもだめし",
"きもち", "きもの", "きゃく", "きやく", "ぎゅうにく", "きよう", "きょうりゅう", "きらい", "きらく", "きりん",
"きれい", "きれつ", "きろく", "ぎろん", "きわめる", "ぎんいろ", "きんかくじ", "きんじょ", "きんようび", "ぐあい",
"くいず", "くうかん", "くうき", "くうぐん", "くうこう", "ぐうせい", "くうそう", "ぐうたら", "くうふく", "くうぼ",
"くかん", "くきょう", "くげん", "ぐこう", "くさい", "くさき", "くさばな", "くさる", "くしゃみ", "くしょう",
"くすのき", "くすりゆび", "くせげ", "くせん", "ぐたいてき", "くださる", "くたびれる", "くちこみ", "くちさき", "くつした",
"ぐっすり", "くつろぐ", "くとうてん", "くどく", "くなん", "くねくね", "くのう", "くふう", "くみあわせ", "くみたてる",
"くめる", "くやくしょ", "くらす", "くらべる", "くるま", "くれる", "くろう", "くわしい", "ぐんかん", "ぐんしょく",
"ぐんたい", "ぐんて", "けあな", "けいかく", "けいけん", "けいこ", "けいさつ", "げいじゅつ", "けいたい", "げいのうじん",
"けいれき", "けいろ", "けおとす", "けおりもの", "げきか", "げきげん", "げきだん", "げきちん", "げきとつ", "げきは",
"げきやく", "げこう", "げこくじょう", "げざい", "けさき", "げざん", "けしき", "けしごむ", "けしょう", "げすと",
"けたば", "けちゃっぷ", "けちらす", "けつあつ", "けつい", "けつえき", "けっこん", "けつじょ", "けっせき", "けってい",
"けつまつ", "げつようび", "げつれい", "けつろん", "げどく", "けとばす", "けとる", "けなげ", "けなす", "けなみ",
"けぬき", "げねつ", "けねん", "けはい", "げひん", "けぶかい", "げぼく", "けまり", "けみかる", "けむし",
"けむり", "けもの", "けらい", "けろけろ", "けわしい", "けんい", "けんえつ", "けんお", "けんか", "げんき",
"けんげん", "けんこう", "けんさく", "けんしゅう", "けんすう", "げんそう", "けんちく", "けんてい", "けんとう", "けんない",
"けんにん", "げんぶつ", "けんま", "けんみん", "けんめい", "けんらん", "けんり", "こあくま", "こいぬ", "こいびと",
"ごうい", "こうえん", "こうおん", "こうかん", "ごうきゅう", "ごうけい", "こうこう", "こうさい", "こうじ", "こうすい",
"ごうせい", "こうそく", "こうたい", "こうちゃ", "こうつう", "こうてい", "こうどう", "こうない", "こうはい", "ごうほう",
"ごうまん", "こうもく", "こうりつ", "こえる", "こおり", "ごかい", "ごがつ", "ごかん", "こくご", "こくさい",
"こくとう", "こくない", "こくはく", "こぐま", "こけい", "こける", "ここのか", "こころ", "こさめ", "こしつ",
"こすう", "こせい", "こせき", "こぜん", "こそだて", "こたい", "こたえる", "こたつ", "こちょう", "こっか",
"こつこつ", "こつばん", "こつぶ", "こてい", "こてん", "ことがら", "ことし", "ことば", "ことり", "こなごな",
"こねこね", "このまま", "このみ", "このよ", "ごはん", "こひつじ", "こふう", "こふん", "こぼれる", "ごまあぶら",
"こまかい", "ごますり", "こまつな", "こまる", "こむぎこ", "こもじ", "こもち", "こもの", "こもん", "こやく",
"こやま", "こゆう", "こゆび", "こよい", "こよう", "こりる", "これくしょん", "ころっけ", "こわもて", "こわれる",
"こんいん", "こんかい", "こんき", "こんしゅう", "こんすい", "こんだて", "こんとん", "こんなん", "こんびに", "こんぽん",
"こんまけ", "こんや", "こんれい", "こんわく", "ざいえき", "さいかい", "さいきん", "ざいげん", "ざいこ", "さいしょ",
"さいせい", "ざいたく", "ざいちゅう", "さいてき", "ざいりょう", "さうな", "さかいし", "さがす", "さかな", "さかみち",
"さがる", "さぎょう", "さくし", "さくひん", "さくら", "さこく", "さこつ", "さずかる", "ざせき", "さたん",
"さつえい", "ざつおん", "ざっか", "ざつがく", "さっきょく", "ざっし", "さつじん", "ざっそう", "さつたば", "さつまいも",
"さてい", "さといも", "さとう", "さとおや", "さとし", "さとる", "さのう", "さばく", "さびしい", "さべつ",
"さほう", "さほど", "さます", "さみしい", "さみだれ", "さむけ", "さめる", "さやえんどう", "さゆう", "さよう",
"さよく", "さらだ", "ざるそば", "さわやか", "さわる", "さんいん", "さんか", "さんきゃく", "さんこう", "さんさい",
"ざんしょ", "さんすう", "さんせい", "さんそ", "さんち", "さんま", "さんみ", "さんらん", "しあい", "しあげ",
"しあさって", "しあわせ", "しいく", "しいん", "しうち", "しえい", "しおけ", "しかい", "しかく", "じかん",
"しごと", "しすう", "じだい", "したうけ", "したぎ", "したて", "したみ", "しちょう", "しちりん", "しっかり",
"しつじ", "しつもん", "してい", "してき", "してつ", "じてん", "じどう", "しなぎれ", "しなもの", "しなん",
"しねま", "しねん", "しのぐ", "しのぶ", "しはい", "しばかり", "しはつ", "しはらい", "しはん", "しひょう",
"しふく", "じぶん", "しへい", "しほう", "しほん", "しまう", "しまる", "しみん", "しむける", "じむしょ",
"しめい", "しめる", "しもん", "しゃいん", "しゃうん", "しゃおん", "じゃがいも", "しやくしょ", "しゃくほう", "しゃけん",
"しゃこ", "しゃざい", "しゃしん", "しゃせん", "しゃそう", "しゃたい", "しゃちょう", "しゃっきん", "じゃま", "しゃりん",
"しゃれい", "じゆう", "じゅうしょ", "しゅくはく", "じゅしん", "しゅっせき", "しゅみ", "しゅらば", "じゅんばん", "しょうかい",
"しょくたく", "しょっけん", "しょどう", "しょもつ", "しらせる", "しらべる", "しんか", "しんこう", "じんじゃ", "しんせいじ",
"しんちく", "しんりん", "すあげ", "すあし", "すあな", "ずあん", "すいえい", "すいか", "すいとう", "ずいぶん",
"すいようび", "すうがく", "すうじつ", "すうせん", "すおどり", "すきま", "すくう", "すくない", "すける", "すごい",
"すこし", "ずさん", "すずしい", "すすむ", "すすめる", "すっかり", "ずっしり", "ずっと", "すてき", "すてる",
"すねる", "すのこ", "すはだ", "すばらしい", "ずひょう", "ずぶぬれ", "すぶり", "すふれ", "すべて", "すべる",
"ずほう", "すぼん", "すまい", "すめし", "すもう", "すやき", "すらすら", "するめ", "すれちがう", "すろっと",
"すわる", "すんぜん", "すんぽう", "せあぶら", "せいかつ", "せいげん", "せいじ", "せいよう", "せおう", "せかいかん",
"せきにん", "せきむ", "せきゆ", "せきらんうん", "せけん", "せこう", "せすじ", "せたい", "せたけ", "せっかく",
"せっきゃく", "ぜっく", "せっけん", "せっこつ", "せっさたくま", "せつぞく", "せつだん", "せつでん", "せっぱん", "せつび",
"せつぶん", "せつめい", "せつりつ", "せなか", "せのび", "せはば", "せびろ", "せぼね", "せまい", "せまる",
"せめる", "せもたれ", "せりふ", "ぜんあく", "せんい", "せんえい", "せんか", "せんきょ", "せんく", "せんげん",
"ぜんご", "せんさい", "せんしゅ", "せんすい", "せんせい", "せんぞ", "せんたく", "せんちょう", "せんてい", "せんとう",
"せんぬき", "せんねん", "せんぱい", "ぜんぶ", "ぜんぽう", "せんむ", "せんめんじょ", "せんもん", "せんやく", "せんゆう",
"せんよう", "ぜんら", "ぜんりゃく", "せんれい", "せんろ", "そあく", "そいとげる", "そいね", "そうがんきょう", "そうき",
"そうご", "そうしん", "そうだん", "そうなん", "そうび", "そうめん", "そうり", "そえもの", "そえん", "そがい",
"そげき", "そこう", "そこそこ", "そざい", "そしな", "そせい", "そせん", "そそぐ", "そだてる", "そつう",
"そつえん", "そっかん", "そつぎょう", "そっけつ", "そっこう", "そっせん", "そっと", "そとがわ", "そとづら", "そなえる",
"そなた", "そふぼ", "そぼく", "そぼろ", "そまつ", "そまる", "そむく", "そむりえ", "そめる", "そもそも",
"そよかぜ", "そらまめ", "そろう", "そんかい", "そんけい", "そんざい", "そんしつ", "そんぞく", "そんちょう", "ぞんび",
"ぞんぶん", "そんみん", "たあい", "たいいん", "たいうん", "たいえき", "たいおう", "だいがく", "たいき", "たいぐう",
"たいけん", "たいこ", "たいざい", "だいじょうぶ", "だいすき", "たいせつ", "たいそう", "だいたい", "たいちょう", "たいてい",
"だいどころ", "たいない", "たいねつ", "たいのう", "たいはん", "だいひょう", "たいふう", "たいへん", "たいほ", "たいまつばな",
"たいみんぐ", "たいむ", "たいめん", "たいやき", "たいよう", "たいら", "たいりょく", "たいる", "たいわん", "たうえ",
"たえる", "たおす", "たおる", "たおれる", "たかい", "たかね", "たきび", "たくさん", "たこく", "たこやき",
"たさい", "たしざん", "だじゃれ", "たすける", "たずさわる", "たそがれ", "たたかう", "たたく", "ただしい", "たたみ",
"たちばな", "だっかい", "だっきゃく", "だっこ", "だっしゅつ", "だったい", "たてる", "たとえる", "たなばた", "たにん",
"たぬき", "たのしみ", "たはつ", "たぶん", "たべる", "たぼう", "たまご", "たまる", "だむる", "ためいき",
"ためす", "ためる", "たもつ", "たやすい", "たよる", "たらす", "たりきほんがん", "たりょう", "たりる", "たると",
"たれる", "たれんと", "たろっと", "たわむれる", "だんあつ", "たんい", "たんおん", "たんか", "たんき", "たんけん",
"たんご", "たんさん", "たんじょうび", "だんせい", "たんそく", "たんたい", "だんち", "たんてい", "たんとう", "だんな",
"たんにん", "だんねつ", "たんのう", "たんぴん", "だんぼう", "たんまつ", "たんめい", "だんれつ", "だんろ", "だんわ",
"ちあい", "ちあん", "ちいき", "ちいさい", "ちえん", "ちかい", "ちから", "ちきゅう", "ちきん", "ちけいず",
"ちけん", "ちこく", "ちさい", "ちしき", "ちしりょう", "ちせい", "ちそう", "ちたい", "ちたん", "ちちおや",
"ちつじょ", "ちてき", "ちてん", "ちぬき", "ちぬり", "ちのう", "ちひょう", "ちへいせん", "ちほう", "ちまた",
"ちみつ", "ちみどろ", "ちめいど", "ちゃんこなべ", "ちゅうい", "ちゆりょく", "ちょうし", "ちょさくけん", "ちらし", "ちらみ",
"ちりがみ", "ちりょう", "ちるど", "ちわわ", "ちんたい", "ちんもく", "ついか", "ついたち", "つうか", "つうじょう",
"つうはん", "つうわ", "つかう", "つかれる", "つくね", "つくる", "つけね", "つける", "つごう", "つたえる",
"つづく", "つつじ", "つつむ", "つとめる", "つながる", "つなみ", "つねづね", "つのる", "つぶす", "つまらない",
"つまる", "つみき", "つめたい", "つもり", "つもる", "つよい", "つるぼ", "つるみく", "つわもの", "つわり",
"てあし", "てあて", "てあみ", "ていおん", "ていか", "ていき", "ていけい", "ていこく", "ていさつ", "ていし",
"ていせい", "ていたい", "ていど", "ていねい", "ていひょう", "ていへん", "ていぼう", "てうち", "ておくれ", "てきとう",
"てくび", "でこぼこ", "てさぎょう", "てさげ", "てすり", "てそう", "てちがい", "てちょう", "てつがく", "てつづき",
"でっぱ", "てつぼう", "てつや", "でぬかえ", "てぬき", "てぬぐい", "てのひら", "てはい", "てぶくろ", "てふだ",
"てほどき", "てほん", "てまえ", "てまきずし", "てみじか", "てみやげ", "てらす", "てれび", "てわけ", "てわたし",
"でんあつ", "てんいん", "てんかい", "てんき", "てんぐ", "てんけん", "てんごく", "てんさい", "てんし", "てんすう",
"でんち", "てんてき", "てんとう", "てんない", "てんぷら", "てんぼうだい", "てんめつ", "てんらんかい", "でんりょく", "でんわ",
"どあい", "といれ", "どうかん", "とうきゅう", "どうぐ", "とうし", "とうむぎ", "とおい", "とおか", "とおく",
"とおす", "とおる", "とかい", "とかす", "ときおり", "ときどき", "とくい", "とくしゅう", "とくてん", "とくに",
"とくべつ", "とけい", "とける", "とこや", "とさか", "としょかん", "とそう", "とたん", "とちゅう", "とっきゅう",
"とっくん", "とつぜん", "とつにゅう", "とどける", "ととのえる", "とない", "となえる", "となり", "とのさま", "とばす",
"どぶがわ", "とほう", "とまる", "とめる", "ともだち", "ともる", "どようび", "とらえる", "とんかつ", "どんぶり",
"ないかく", "ないこう", "ないしょ", "ないす", "ないせん", "ないそう", "なおす", "ながい", "なくす", "なげる",
"なこうど", "なさけ", "なたでここ", "なっとう", "なつやすみ", "ななおし", "なにごと", "なにもの", "なにわ", "なのか",
"なふだ", "なまいき", "なまえ", "なまみ", "なみだ", "なめらか", "なめる", "なやむ", "ならう", "ならび",
"ならぶ", "なれる", "なわとび", "なわばり", "にあう", "にいがた", "にうけ", "におい", "にかい", "にがて",
"にきび", "にくしみ", "にくまん", "にげる", "にさんかたんそ", "にしき", "にせもの", "にちじょう", "にちようび", "にっか",
"にっき", "にっけい", "にっこう", "にっさん", "にっしょく", "にっすう", "にっせき", "にってい", "になう", "にほん",
"にまめ", "にもつ", "にやり", "にゅういん", "にりんしゃ", "にわとり", "にんい", "にんか", "にんき", "にんげん",
"にんしき", "にんずう", "にんそう", "にんたい", "にんち", "にんてい", "にんにく", "にんぷ", "にんまり", "にんむ",
"にんめい", "にんよう", "ぬいくぎ", "ぬかす", "ぬぐいとる", "ぬぐう", "ぬくもり", "ぬすむ", "ぬまえび", "ぬめり",
"ぬらす", "ぬんちゃく", "ねあげ", "ねいき", "ねいる", "ねいろ", "ねぐせ", "ねくたい", "ねくら", "ねこぜ",
"ねこむ", "ねさげ", "ねすごす", "ねそべる", "ねだん", "ねつい", "ねっしん", "ねつぞう", "ねったいぎょ", "ねぶそく",
"ねふだ", "ねぼう", "ねほりはほり", "ねまき", "ねまわし", "ねみみ", "ねむい", "ねむたい", "ねもと", "ねらう",
"ねわざ", "ねんいり", "ねんおし", "ねんかん", "ねんきん", "ねんぐ", "ねんざ", "ねんし", "ねんちゃく", "ねんど",
"ねんぴ", "ねんぶつ", "ねんまつ", "ねんりょう", "ねんれい", "のいず", "のおづま", "のがす", "のきなみ", "のこぎり",
"のこす", "のこる", "のせる", "のぞく", "のぞむ", "のたまう", "のちほど", "のっく", "のばす", "のはら",
"のべる", "のぼる", "のみもの", "のやま", "のらいぬ", "のらねこ", "のりもの", "のりゆき", "のれん", "のんき",
"ばあい", "はあく", "ばあさん", "ばいか", "ばいく", "はいけん", "はいご", "はいしん", "はいすい", "はいせん",
"はいそう", "はいち", "ばいばい", "はいれつ", "はえる", "はおる", "はかい", "ばかり", "はかる", "はくしゅ",
"はけん", "はこぶ", "はさみ", "はさん", "はしご", "ばしょ", "はしる", "はせる", "ぱそこん", "はそん",
"はたん", "はちみつ", "はつおん", "はっかく", "はづき", "はっきり", "はっくつ", "はっけん", "はっこう", "はっさん",
"はっしん", "はったつ", "はっちゅう", "はってん", "はっぴょう", "はっぽう", "はなす", "はなび", "はにかむ", "はぶらし",
"はみがき", "はむかう", "はめつ", "はやい", "はやし", "はらう", "はろうぃん", "はわい", "はんい", "はんえい",
"はんおん", "はんかく", "はんきょう", "ばんぐみ", "はんこ", "はんしゃ", "はんすう", "はんだん", "ぱんち", "ぱんつ",
"はんてい", "はんとし", "はんのう", "はんぱ", "はんぶん", "はんぺん", "はんぼうき", "はんめい", "はんらん", "はんろん",
"ひいき", "ひうん", "ひえる", "ひかく", "ひかり", "ひかる", "ひかん", "ひくい", "ひけつ", "ひこうき",
"ひこく", "ひさい", "ひさしぶり", "ひさん", "びじゅつかん", "ひしょ", "ひそか", "ひそむ", "ひたむき", "ひだり",
"ひたる", "ひつぎ", "ひっこし", "ひっし", "ひつじゅひん", "ひっす", "ひつぜん", "ぴったり", "ぴっちり", "ひつよう",
"ひてい", "ひとごみ", "ひなまつり", "ひなん", "ひねる", "ひはん", "ひびく", "ひひょう", "ひほう", "ひまわり",
"ひまん", "ひみつ", "ひめい", "ひめじし", "ひやけ", "ひやす", "ひよう", "びょうき", "ひらがな", "ひらく",
"ひりつ", "ひりょう", "ひるま", "ひるやすみ", "ひれい", "ひろい", "ひろう", "ひろき", "ひろゆき", "ひんかく",
"ひんけつ", "ひんこん", "ひんしゅ", "ひんそう", "ぴんち", "ひんぱん", "びんぼう", "ふあん", "ふいうち", "ふうけい",
"ふうせん", "ぷうたろう", "ふうとう", "ふうふ", "ふえる", "ふおん", "ふかい", "ふきん", "ふくざつ", "ふくぶくろ",
"ふこう", "ふさい", "ふしぎ", "ふじみ", "ふすま", "ふせい", "ふせぐ", "ふそく", "ぶたにく", "ふたん",
"ふちょう", "ふつう", "ふつか", "ふっかつ", "ふっき", "ふっこく", "ぶどう", "ふとる", "ふとん", "ふのう",
"ふはい", "ふひょう", "ふへん", "ふまん", "ふみん", "ふめつ", "ふめん", "ふよう", "ふりこ", "ふりる",
"ふるい", "ふんいき", "ぶんがく", "ぶんぐ", "ふんしつ", "ぶんせき", "ふんそう", "ぶんぽう", "へいあん", "へいおん",
"へいがい", "へいき", "へいげん", "へいこう", "へいさ", "へいしゃ", "へいせつ", "へいそ", "へいたく", "へいてん",
"へいねつ", "へいわ", "へきが", "へこむ", "べにいろ", "べにしょうが", "へらす", "へんかん", "べんきょう", "べんごし",
"へんさい", "へんたい", "べんり", "ほあん", "ほいく", "ぼうぎょ", "ほうこく", "ほうそう", "ほうほう", "ほうもん",
"ほうりつ", "ほえる", "ほおん", "ほかん", "ほきょう", "ぼきん", "ほくろ", "ほけつ", "ほけん", "ほこう",
"ほこる", "ほしい", "ほしつ", "ほしゅ", "ほしょう", "ほせい", "ほそい", "ほそく", "ほたて", "ほたる",
"ぽちぶくろ", "ほっきょく", "ほっさ", "ほったん", "ほとんど", "ほめる", "ほんい", "ほんき", "ほんけ", "ほんしつ",
"ほんやく", "まいにち", "まかい", "まかせる", "まがる", "まける", "まこと", "まさつ", "まじめ", "ますく",
"まぜる", "まつり", "まとめ", "まなぶ", "まぬけ", "まねく", "まほう", "まもる", "まゆげ", "まよう",
"まろやか", "まわす", "まわり", "まわる", "まんが", "まんきつ", "まんぞく", "まんなか", "みいら", "みうち",
"みえる", "みがく", "みかた", "みかん", "みけん", "みこん", "みじかい", "みすい", "みすえる", "みせる",
"みっか", "みつかる", "みつける", "みてい", "みとめる", "みなと", "みなみかさい", "みねらる", "みのう", "みのがす",
"みほん", "みもと", "みやげ", "みらい", "みりょく", "みわく", "みんか", "みんぞく", "むいか", "むえき",
"むえん", "むかい", "むかう", "むかえ", "むかし", "むぎちゃ", "むける", "むげん", "むさぼる", "むしあつい",
"むしば", "むじゅん", "むしろ", "むすう", "むすこ", "むすぶ", "むすめ", "むせる", "むせん", "むちゅう",
"むなしい", "むのう", "むやみ", "むよう", "むらさき", "むりょう", "むろん", "めいあん", "めいうん", "めいえん",
"めいかく", "めいきょく", "めいさい", "めいし", "めいそう", "めいぶつ", "めいれい", "めいわく", "めぐまれる", "めざす",
"めした", "めずらしい", "めだつ", "めまい", "めやす", "めんきょ", "めんせき", "めんどう", "もうしあげる", "もうどうけん",
"もえる", "もくし", "もくてき", "もくようび", "もちろん", "もどる", "もらう", "もんく", "もんだい", "やおや",
"やける", "やさい", "やさしい", "やすい", "やすたろう", "やすみ", "やせる", "やそう", "やたい", "やちん",
"やっと", "やっぱり", "やぶる", "やめる", "ややこしい", "やよい", "やわらかい", "ゆうき", "ゆうびんきょく", "ゆうべ",
"ゆうめい", "ゆけつ", "ゆしゅつ", "ゆせん", "ゆそう", "ゆたか", "ゆちゃく", "ゆでる", "ゆにゅう", "ゆびわ",
"ゆらい", "ゆれる", "ようい", "ようか", "ようきゅう", "ようじ", "ようす", "ようちえん", "よかぜ", "よかん",
"よきん", "よくせい", "よくぼう", "よけい", "よごれる", "よさん", "よしゅう", "よそう", "よそく", "よっか",
"よてい", "よどがわく", "よねつ", "よやく", "よゆう", "よろこぶ", "よろしい", "らいう", "らくがき", "らくご",
"らくさつ", "らくだ", "らしんばん", "らせん", "らぞく", "らたい", "らっか", "られつ", "りえき", "りかい",
"りきさく", "りきせつ", "りくぐん", "りくつ", "りけん", "りこう", "りせい", "りそう", "りそく", "りてん",
"りねん", "りゆう", "りゅうがく", "りよう", "りょうり", "りょかん", "りょくちゃ", "りょこう", "りりく", "りれき",
"りろん", "りんご", "るいけい", "るいさい", "るいじ", "るいせき", "るすばん", "るりがわら", "れいかん", "れいぎ",
"れいせい", "れいぞうこ", "れいとう", "れいぼう", "れきし", "れきだい", "れんあい", "れんけい", "れんこん", "れんさい",
"れんしゅう", "れんぞく", "れんらく", "ろうか", "ろうご", "ろうじん", "ろうそく", "ろくが", "ろこつ", "ろじうら",
"ろしゅつ", "ろせん", "ろてん", "ろめん", "ろれつ", "ろんぎ", "ろんぱ", "ろんぶん", "ろんり", "わかす",
"わかめ", "わかやま", "わかれる", "わしつ", "わじまし", "わすれもの", "わらう", "われる"]
</script>
        <script>WORDLISTS = typeof WORDLISTS == "undefined" ? {} : WORDLISTS;
WORDLISTS["spanish"] = [
"ábaco", "abdomen", "abeja", "abierto", "abogado", "abono", "aborto", "abrazo", "abrir", "abuelo",
"abuso", "acabar", "academia", "acceso", "acción", "aceite", "acelga", "acento", "aceptar", "ácido",
"aclarar", "acné", "acoger", "acoso", "activo", "acto", "actriz", "actuar", "acudir", "acuerdo",
"acusar", "adicto", "admitir", "adoptar", "adorno", "aduana", "adulto", "aéreo", "afectar", "afición",
"afinar", "afirmar", "ágil", "agitar", "agonía", "agosto", "agotar", "agregar", "agrio", "agua",
"agudo", "águila", "aguja", "ahogo", "ahorro", "aire", "aislar", "ajedrez", "ajeno", "ajuste",
"alacrán", "alambre", "alarma", "alba", "álbum", "alcalde", "aldea", "alegre", "alejar", "alerta",
"aleta", "alfiler", "alga", "algodón", "aliado", "aliento", "alivio", "alma", "almeja", "almíbar",
"altar", "alteza", "altivo", "alto", "altura", "alumno", "alzar", "amable", "amante", "amapola",
"amargo", "amasar", "ámbar", "ámbito", "ameno", "amigo", "amistad", "amor", "amparo", "amplio",
"ancho", "anciano", "ancla", "andar", "andén", "anemia", "ángulo", "anillo", "ánimo", "anís",
"anotar", "antena", "antiguo", "antojo", "anual", "anular", "anuncio", "añadir", "añejo", "año",
"apagar", "aparato", "apetito", "apio", "aplicar", "apodo", "aporte", "apoyo", "aprender", "aprobar",
"apuesta", "apuro", "arado", "araña", "arar", "árbitro", "árbol", "arbusto", "archivo", "arco",
"arder", "ardilla", "arduo", "área", "árido", "aries", "armonía", "arnés", "aroma", "arpa",
"arpón", "arreglo", "arroz", "arruga", "arte", "artista", "asa", "asado", "asalto", "ascenso",
"asegurar", "aseo", "asesor", "asiento", "asilo", "asistir", "asno", "asombro", "áspero", "astilla",
"astro", "astuto", "asumir", "asunto", "atajo", "ataque", "atar", "atento", "ateo", "ático",
"atleta", "átomo", "atraer", "atroz", "atún", "audaz", "audio", "auge", "aula", "aumento",
"ausente", "autor", "aval", "avance", "avaro", "ave", "avellana", "avena", "avestruz", "avión",
"aviso", "ayer", "ayuda", "ayuno", "azafrán", "azar", "azote", "azúcar", "azufre", "azul",
"baba", "babor", "bache", "bahía", "baile", "bajar", "balanza", "balcón", "balde", "bambú",
"banco", "banda", "baño", "barba", "barco", "barniz", "barro", "báscula", "bastón", "basura",
"batalla", "batería", "batir", "batuta", "baúl", "bazar", "bebé", "bebida", "bello", "besar",
"beso", "bestia", "bicho", "bien", "bingo", "blanco", "bloque", "blusa", "boa", "bobina",
"bobo", "boca", "bocina", "boda", "bodega", "boina", "bola", "bolero", "bolsa", "bomba",
"bondad", "bonito", "bono", "bonsái", "borde", "borrar", "bosque", "bote", "botín", "bóveda",
"bozal", "bravo", "brazo", "brecha", "breve", "brillo", "brinco", "brisa", "broca", "broma",
"bronce", "brote", "bruja", "brusco", "bruto", "buceo", "bucle", "bueno", "buey", "bufanda",
"bufón", "búho", "buitre", "bulto", "burbuja", "burla", "burro", "buscar", "butaca", "buzón",
"caballo", "cabeza", "cabina", "cabra", "cacao", "cadáver", "cadena", "caer", "café", "caída",
"caimán", "caja", "cajón", "cal", "calamar", "calcio", "caldo", "calidad", "calle", "calma",
"calor", "calvo", "cama", "cambio", "camello", "camino", "campo", "cáncer", "candil", "canela",
"canguro", "canica", "canto", "caña", "cañón", "caoba", "caos", "capaz", "capitán", "capote",
"captar", "capucha", "cara", "carbón", "cárcel", "careta", "carga", "cariño", "carne", "carpeta",
"carro", "carta", "casa", "casco", "casero", "caspa", "castor", "catorce", "catre", "caudal",
"causa", "cazo", "cebolla", "ceder", "cedro", "celda", "célebre", "celoso", "célula", "cemento",
"ceniza", "centro", "cerca", "cerdo", "cereza", "cero", "cerrar", "certeza", "césped", "cetro",
"chacal", "chaleco", "champú", "chancla", "chapa", "charla", "chico", "chiste", "chivo", "choque",
"choza", "chuleta", "chupar", "ciclón", "ciego", "cielo", "cien", "cierto", "cifra", "cigarro",
"cima", "cinco", "cine", "cinta", "ciprés", "circo", "ciruela", "cisne", "cita", "ciudad",
"clamor", "clan", "claro", "clase", "clave", "cliente", "clima", "clínica", "cobre", "cocción",
"cochino", "cocina", "coco", "código", "codo", "cofre", "coger", "cohete", "cojín", "cojo",
"cola", "colcha", "colegio", "colgar", "colina", "collar", "colmo", "columna", "combate", "comer",
"comida", "cómodo", "compra", "conde", "conejo", "conga", "conocer", "consejo", "contar", "copa",
"copia", "corazón", "corbata", "corcho", "cordón", "corona", "correr", "coser", "cosmos", "costa",
"cráneo", "cráter", "crear", "crecer", "creído", "crema", "cría", "crimen", "cripta", "crisis",
"cromo", "crónica", "croqueta", "crudo", "cruz", "cuadro", "cuarto", "cuatro", "cubo", "cubrir",
"cuchara", "cuello", "cuento", "cuerda", "cuesta", "cueva", "cuidar", "culebra", "culpa", "culto",
"cumbre", "cumplir", "cuna", "cuneta", "cuota", "cupón", "cúpula", "curar", "curioso", "curso",
"curva", "cutis", "dama", "danza", "dar", "dardo", "dátil", "deber", "débil", "década",
"decir", "dedo", "defensa", "definir", "dejar", "delfín", "delgado", "delito", "demora", "denso",
"dental", "deporte", "derecho", "derrota", "desayuno", "deseo", "desfile", "desnudo", "destino", "desvío",
"detalle", "detener", "deuda", "día", "diablo", "diadema", "diamante", "diana", "diario", "dibujo",
"dictar", "diente", "dieta", "diez", "difícil", "digno", "dilema", "diluir", "dinero", "directo",
"dirigir", "disco", "diseño", "disfraz", "diva", "divino", "doble", "doce", "dolor", "domingo",
"don", "donar", "dorado", "dormir", "dorso", "dos", "dosis", "dragón", "droga", "ducha",
"duda", "duelo", "dueño", "dulce", "dúo", "duque", "durar", "dureza", "duro", "ébano",
"ebrio", "echar", "eco", "ecuador", "edad", "edición", "edificio", "editor", "educar", "efecto",
"eficaz", "eje", "ejemplo", "elefante", "elegir", "elemento", "elevar", "elipse", "élite", "elixir",
"elogio", "eludir", "embudo", "emitir", "emoción", "empate", "empeño", "empleo", "empresa", "enano",
"encargo", "enchufe", "encía", "enemigo", "enero", "enfado", "enfermo", "engaño", "enigma", "enlace",
"enorme", "enredo", "ensayo", "enseñar", "entero", "entrar", "envase", "envío", "época", "equipo",
"erizo", "escala", "escena", "escolar", "escribir", "escudo", "esencia", "esfera", "esfuerzo", "espada",
"espejo", "espía", "esposa", "espuma", "esquí", "estar", "este", "estilo", "estufa", "etapa",
"eterno", "ética", "etnia", "evadir", "evaluar", "evento", "evitar", "exacto", "examen", "exceso",
"excusa", "exento", "exigir", "exilio", "existir", "éxito", "experto", "explicar", "exponer", "extremo",
"fábrica", "fábula", "fachada", "fácil", "factor", "faena", "faja", "falda", "fallo", "falso",
"faltar", "fama", "familia", "famoso", "faraón", "farmacia", "farol", "farsa", "fase", "fatiga",
"fauna", "favor", "fax", "febrero", "fecha", "feliz", "feo", "feria", "feroz", "fértil",
"fervor", "festín", "fiable", "fianza", "fiar", "fibra", "ficción", "ficha", "fideo", "fiebre",
"fiel", "fiera", "fiesta", "figura", "fijar", "fijo", "fila", "filete", "filial", "filtro",
"fin", "finca", "fingir", "finito", "firma", "flaco", "flauta", "flecha", "flor", "flota",
"fluir", "flujo", "flúor", "fobia", "foca", "fogata", "fogón", "folio", "folleto", "fondo",
"forma", "forro", "fortuna", "forzar", "fosa", "foto", "fracaso", "frágil", "franja", "frase",
"fraude", "freír", "freno", "fresa", "frío", "frito", "fruta", "fuego", "fuente", "fuerza",
"fuga", "fumar", "función", "funda", "furgón", "furia", "fusil", "fútbol", "futuro", "gacela",
"gafas", "gaita", "gajo", "gala", "galería", "gallo", "gamba", "ganar", "gancho", "ganga",
"ganso", "garaje", "garza", "gasolina", "gastar", "gato", "gavilán", "gemelo", "gemir", "gen",
"género", "genio", "gente", "geranio", "gerente", "germen", "gesto", "gigante", "gimnasio", "girar",
"giro", "glaciar", "globo", "gloria", "gol", "golfo", "goloso", "golpe", "goma", "gordo",
"gorila", "gorra", "gota", "goteo", "gozar", "grada", "gráfico", "grano", "grasa", "gratis",
"grave", "grieta", "grillo", "gripe", "gris", "grito", "grosor", "grúa", "grueso", "grumo",
"grupo", "guante", "guapo", "guardia", "guerra", "guía", "guiño", "guion", "guiso", "guitarra",
"gusano", "gustar", "haber", "hábil", "hablar", "hacer", "hacha", "hada", "hallar", "hamaca",
"harina", "haz", "hazaña", "hebilla", "hebra", "hecho", "helado", "helio", "hembra", "herir",
"hermano", "héroe", "hervir", "hielo", "hierro", "hígado", "higiene", "hijo", "himno", "historia",
"hocico", "hogar", "hoguera", "hoja", "hombre", "hongo", "honor", "honra", "hora", "hormiga",
"horno", "hostil", "hoyo", "hueco", "huelga", "huerta", "hueso", "huevo", "huida", "huir",
"humano", "húmedo", "humilde", "humo", "hundir", "huracán", "hurto", "icono", "ideal", "idioma",
"ídolo", "iglesia", "iglú", "igual", "ilegal", "ilusión", "imagen", "imán", "imitar", "impar",
"imperio", "imponer", "impulso", "incapaz", "índice", "inerte", "infiel", "informe", "ingenio", "inicio",
"inmenso", "inmune", "innato", "insecto", "instante", "interés", "íntimo", "intuir", "inútil", "invierno",
"ira", "iris", "ironía", "isla", "islote", "jabalí", "jabón", "jamón", "jarabe", "jardín",
"jarra", "jaula", "jazmín", "jefe", "jeringa", "jinete", "jornada", "joroba", "joven", "joya",
"juerga", "jueves", "juez", "jugador", "jugo", "juguete", "juicio", "junco", "jungla", "junio",
"juntar", "júpiter", "jurar", "justo", "juvenil", "juzgar", "kilo", "koala", "labio", "lacio",
"lacra", "lado", "ladrón", "lagarto", "lágrima", "laguna", "laico", "lamer", "lámina", "lámpara",
"lana", "lancha", "langosta", "lanza", "lápiz", "largo", "larva", "lástima", "lata", "látex",
"latir", "laurel", "lavar", "lazo", "leal", "lección", "leche", "lector", "leer", "legión",
"legumbre", "lejano", "lengua", "lento", "leña", "león", "leopardo", "lesión", "letal", "letra",
"leve", "leyenda", "libertad", "libro", "licor", "líder", "lidiar", "lienzo", "liga", "ligero",
"lima", "límite", "limón", "limpio", "lince", "lindo", "línea", "lingote", "lino", "linterna",
"líquido", "liso", "lista", "litera", "litio", "litro", "llaga", "llama", "llanto", "llave",
"llegar", "llenar", "llevar", "llorar", "llover", "lluvia", "lobo", "loción", "loco", "locura",
"lógica", "logro", "lombriz", "lomo", "lonja", "lote", "lucha", "lucir", "lugar", "lujo",
"luna", "lunes", "lupa", "lustro", "luto", "luz", "maceta", "macho", "madera", "madre",
"maduro", "maestro", "mafia", "magia", "mago", "maíz", "maldad", "maleta", "malla", "malo",
"mamá", "mambo", "mamut", "manco", "mando", "manejar", "manga", "maniquí", "manjar", "mano",
"manso", "manta", "mañana", "mapa", "máquina", "mar", "marco", "marea", "marfil", "margen",
"marido", "mármol", "marrón", "martes", "marzo", "masa", "máscara", "masivo", "matar", "materia",
"matiz", "matriz", "máximo", "mayor", "mazorca", "mecha", "medalla", "medio", "médula", "mejilla",
"mejor", "melena", "melón", "memoria", "menor", "mensaje", "mente", "menú", "mercado", "merengue",
"mérito", "mes", "mesón", "meta", "meter", "método", "metro", "mezcla", "miedo", "miel",
"miembro", "miga", "mil", "milagro", "militar", "millón", "mimo", "mina", "minero", "mínimo",
"minuto", "miope", "mirar", "misa", "miseria", "misil", "mismo", "mitad", "mito", "mochila",
"moción", "moda", "modelo", "moho", "mojar", "molde", "moler", "molino", "momento", "momia",
"monarca", "moneda", "monja", "monto", "moño", "morada", "morder", "moreno", "morir", "morro",
"morsa", "mortal", "mosca", "mostrar", "motivo", "mover", "móvil", "mozo", "mucho", "mudar",
"mueble", "muela", "muerte", "muestra", "mugre", "mujer", "mula", "muleta", "multa", "mundo",
"muñeca", "mural", "muro", "músculo", "museo", "musgo", "música", "muslo", "nácar", "nación",
"nadar", "naipe", "naranja", "nariz", "narrar", "nasal", "natal", "nativo", "natural", "náusea",
"naval", "nave", "navidad", "necio", "néctar", "negar", "negocio", "negro", "neón", "nervio",
"neto", "neutro", "nevar", "nevera", "nicho", "nido", "niebla", "nieto", "niñez", "niño",
"nítido", "nivel", "nobleza", "noche", "nómina", "noria", "norma", "norte", "nota", "noticia",
"novato", "novela", "novio", "nube", "nuca", "núcleo", "nudillo", "nudo", "nuera", "nueve",
"nuez", "nulo", "número", "nutria", "oasis", "obeso", "obispo", "objeto", "obra", "obrero",
"observar", "obtener", "obvio", "oca", "ocaso", "océano", "ochenta", "ocho", "ocio", "ocre",
"octavo", "octubre", "oculto", "ocupar", "ocurrir", "odiar", "odio", "odisea", "oeste", "ofensa",
"oferta", "oficio", "ofrecer", "ogro", "oído", "oír", "ojo", "ola", "oleada", "olfato",
"olivo", "olla", "olmo", "olor", "olvido", "ombligo", "onda", "onza", "opaco", "opción",
"ópera", "opinar", "oponer", "optar", "óptica", "opuesto", "oración", "orador", "oral", "órbita",
"orca", "orden", "oreja", "órgano", "orgía", "orgullo", "oriente", "origen", "orilla", "oro",
"orquesta", "oruga", "osadía", "oscuro", "osezno", "oso", "ostra", "otoño", "otro", "oveja",
"óvulo", "óxido", "oxígeno", "oyente", "ozono", "pacto", "padre", "paella", "página", "pago",
"país", "pájaro", "palabra", "palco", "paleta", "pálido", "palma", "paloma", "palpar", "pan",
"panal", "pánico", "pantera", "pañuelo", "papá", "papel", "papilla", "paquete", "parar", "parcela",
"pared", "parir", "paro", "párpado", "parque", "párrafo", "parte", "pasar", "paseo", "pasión",
"paso", "pasta", "pata", "patio", "patria", "pausa", "pauta", "pavo", "payaso", "peatón",
"pecado", "pecera", "pecho", "pedal", "pedir", "pegar", "peine", "pelar", "peldaño", "pelea",
"peligro", "pellejo", "pelo", "peluca", "pena", "pensar", "peñón", "peón", "peor", "pepino",
"pequeño", "pera", "percha", "perder", "pereza", "perfil", "perico", "perla", "permiso", "perro",
"persona", "pesa", "pesca", "pésimo", "pestaña", "pétalo", "petróleo", "pez", "pezuña", "picar",
"pichón", "pie", "piedra", "pierna", "pieza", "pijama", "pilar", "piloto", "pimienta", "pino",
"pintor", "pinza", "piña", "piojo", "pipa", "pirata", "pisar", "piscina", "piso", "pista",
"pitón", "pizca", "placa", "plan", "plata", "playa", "plaza", "pleito", "pleno", "plomo",
"pluma", "plural", "pobre", "poco", "poder", "podio", "poema", "poesía", "poeta", "polen",
"policía", "pollo", "polvo", "pomada", "pomelo", "pomo", "pompa", "poner", "porción", "portal",
"posada", "poseer", "posible", "poste", "potencia", "potro", "pozo", "prado", "precoz", "pregunta",
"premio", "prensa", "preso", "previo", "primo", "príncipe", "prisión", "privar", "proa", "probar",
"proceso", "producto", "proeza", "profesor", "programa", "prole", "promesa", "pronto", "propio", "próximo",
"prueba", "público", "puchero", "pudor", "pueblo", "puerta", "puesto", "pulga", "pulir", "pulmón",
"pulpo", "pulso", "puma", "punto", "puñal", "puño", "pupa", "pupila", "puré", "quedar",
"queja", "quemar", "querer", "queso", "quieto", "química", "quince", "quitar", "rábano", "rabia",
"rabo", "ración", "radical", "raíz", "rama", "rampa", "rancho", "rango", "rapaz", "rápido",
"rapto", "rasgo", "raspa", "rato", "rayo", "raza", "razón", "reacción", "realidad", "rebaño",
"rebote", "recaer", "receta", "rechazo", "recoger", "recreo", "recto", "recurso", "red", "redondo",
"reducir", "reflejo", "reforma", "refrán", "refugio", "regalo", "regir", "regla", "regreso", "rehén",
"reino", "reír", "reja", "relato", "relevo", "relieve", "relleno", "reloj", "remar", "remedio",
"remo", "rencor", "rendir", "renta", "reparto", "repetir", "reposo", "reptil", "res", "rescate",
"resina", "respeto", "resto", "resumen", "retiro", "retorno", "retrato", "reunir", "revés", "revista",
"rey", "rezar", "rico", "riego", "rienda", "riesgo", "rifa", "rígido", "rigor", "rincón",
"riñón", "río", "riqueza", "risa", "ritmo", "rito", "rizo", "roble", "roce", "rociar",
"rodar", "rodeo", "rodilla", "roer", "rojizo", "rojo", "romero", "romper", "ron", "ronco",
"ronda", "ropa", "ropero", "rosa", "rosca", "rostro", "rotar", "rubí", "rubor", "rudo",
"rueda", "rugir", "ruido", "ruina", "ruleta", "rulo", "rumbo", "rumor", "ruptura", "ruta",
"rutina", "sábado", "saber", "sabio", "sable", "sacar", "sagaz", "sagrado", "sala", "saldo",
"salero", "salir", "salmón", "salón", "salsa", "salto", "salud", "salvar", "samba", "sanción",
"sandía", "sanear", "sangre", "sanidad", "sano", "santo", "sapo", "saque", "sardina", "sartén",
"sastre", "satán", "sauna", "saxofón", "sección", "seco", "secreto", "secta", "sed", "seguir",
"seis", "sello", "selva", "semana", "semilla", "senda", "sensor", "señal", "señor", "separar",
"sepia", "sequía", "ser", "serie", "sermón", "servir", "sesenta", "sesión", "seta", "setenta",
"severo", "sexo", "sexto", "sidra", "siesta", "siete", "siglo", "signo", "sílaba", "silbar",
"silencio", "silla", "símbolo", "simio", "sirena", "sistema", "sitio", "situar", "sobre", "socio",
"sodio", "sol", "solapa", "soldado", "soledad", "sólido", "soltar", "solución", "sombra", "sondeo",
"sonido", "sonoro", "sonrisa", "sopa", "soplar", "soporte", "sordo", "sorpresa", "sorteo", "sostén",
"sótano", "suave", "subir", "suceso", "sudor", "suegra", "suelo", "sueño", "suerte", "sufrir",
"sujeto", "sultán", "sumar", "superar", "suplir", "suponer", "supremo", "sur", "surco", "sureño",
"surgir", "susto", "sutil", "tabaco", "tabique", "tabla", "tabú", "taco", "tacto", "tajo",
"talar", "talco", "talento", "talla", "talón", "tamaño", "tambor", "tango", "tanque", "tapa",
"tapete", "tapia", "tapón", "taquilla", "tarde", "tarea", "tarifa", "tarjeta", "tarot", "tarro",
"tarta", "tatuaje", "tauro", "taza", "tazón", "teatro", "techo", "tecla", "técnica", "tejado",
"tejer", "tejido", "tela", "teléfono", "tema", "temor", "templo", "tenaz", "tender", "tener",
"tenis", "tenso", "teoría", "terapia", "terco", "término", "ternura", "terror", "tesis", "tesoro",
"testigo", "tetera", "texto", "tez", "tibio", "tiburón", "tiempo", "tienda", "tierra", "tieso",
"tigre", "tijera", "tilde", "timbre", "tímido", "timo", "tinta", "tío", "típico", "tipo",
"tira", "tirón", "titán", "títere", "título", "tiza", "toalla", "tobillo", "tocar", "tocino",
"todo", "toga", "toldo", "tomar", "tono", "tonto", "topar", "tope", "toque", "tórax",
"torero", "tormenta", "torneo", "toro", "torpedo", "torre", "torso", "tortuga", "tos", "tosco",
"toser", "tóxico", "trabajo", "tractor", "traer", "tráfico", "trago", "traje", "tramo", "trance",
"trato", "trauma", "trazar", "trébol", "tregua", "treinta", "tren", "trepar", "tres", "tribu",
"trigo", "tripa", "triste", "triunfo", "trofeo", "trompa", "tronco", "tropa", "trote", "trozo",
"truco", "trueno", "trufa", "tubería", "tubo", "tuerto", "tumba", "tumor", "túnel", "túnica",
"turbina", "turismo", "turno", "tutor", "ubicar", "úlcera", "umbral", "unidad", "unir", "universo",
"uno", "untar", "uña", "urbano", "urbe", "urgente", "urna", "usar", "usuario", "útil",
"utopía", "uva", "vaca", "vacío", "vacuna", "vagar", "vago", "vaina", "vajilla", "vale",
"válido", "valle", "valor", "válvula", "vampiro", "vara", "variar", "varón", "vaso", "vecino",
"vector", "vehículo", "veinte", "vejez", "vela", "velero", "veloz", "vena", "vencer", "venda",
"veneno", "vengar", "venir", "venta", "venus", "ver", "verano", "verbo", "verde", "vereda",
"verja", "verso", "verter", "vía", "viaje", "vibrar", "vicio", "víctima", "vida", "vídeo",
"vidrio", "viejo", "viernes", "vigor", "vil", "villa", "vinagre", "vino", "viñedo", "violín",
"viral", "virgo", "virtud", "visor", "víspera", "vista", "vitamina", "viudo", "vivaz", "vivero",
"vivir", "vivo", "volcán", "volumen", "volver", "voraz", "votar", "voto", "voz", "vuelo",
"vulgar", "yacer", "yate", "yegua", "yema", "yerno", "yeso", "yodo", "yoga", "yogur",
"zafiro", "zanja", "zapato", "zarza", "zona", "zorro", "zumo", "zurdo"]
</script>
        <script>WORDLISTS = typeof WORDLISTS == "undefined" ? {} : WORDLISTS;
WORDLISTS["chinese_simplified"] = [
"的", "一", "是", "在", "不", "了", "有", "和", "人", "这",
"中", "大", "为", "上", "个", "国", "我", "以", "要", "他",
"时", "来", "用", "们", "生", "到", "作", "地", "于", "出",
"就", "分", "对", "成", "会", "可", "主", "发", "年", "动",
"同", "工", "也", "能", "下", "过", "子", "说", "产", "种",
"面", "而", "方", "后", "多", "定", "行", "学", "法", "所",
"民", "得", "经", "十", "三", "之", "进", "着", "等", "部",
"度", "家", "电", "力", "里", "如", "水", "化", "高", "自",
"二", "理", "起", "小", "物", "现", "实", "加", "量", "都",
"两", "体", "制", "机", "当", "使", "点", "从", "业", "本",
"去", "把", "性", "好", "应", "开", "它", "合", "还", "因",
"由", "其", "些", "然", "前", "外", "天", "政", "四", "日",
"那", "社", "义", "事", "平", "形", "相", "全", "表", "间",
"样", "与", "关", "各", "重", "新", "线", "内", "数", "正",
"心", "反", "你", "明", "看", "原", "又", "么", "利", "比",
"或", "但", "质", "气", "第", "向", "道", "命", "此", "变",
"条", "只", "没", "结", "解", "问", "意", "建", "月", "公",
"无", "系", "军", "很", "情", "者", "最", "立", "代", "想",
"已", "通", "并", "提", "直", "题", "党", "程", "展", "五",
"果", "料", "象", "员", "革", "位", "入", "常", "文", "总",
"次", "品", "式", "活", "设", "及", "管", "特", "件", "长",
"求", "老", "头", "基", "资", "边", "流", "路", "级", "少",
"图", "山", "统", "接", "知", "较", "将", "组", "见", "计",
"别", "她", "手", "角", "期", "根", "论", "运", "农", "指",
"几", "九", "区", "强", "放", "决", "西", "被", "干", "做",
"必", "战", "先", "回", "则", "任", "取", "据", "处", "队",
"南", "给", "色", "光", "门", "即", "保", "治", "北", "造",
"百", "规", "热", "领", "七", "海", "口", "东", "导", "器",
"压", "志", "世", "金", "增", "争", "济", "阶", "油", "思",
"术", "极", "交", "受", "联", "什", "认", "六", "共", "权",
"收", "证", "改", "清", "美", "再", "采", "转", "更", "单",
"风", "切", "打", "白", "教", "速", "花", "带", "安", "场",
"身", "车", "例", "真", "务", "具", "万", "每", "目", "至",
"达", "走", "积", "示", "议", "声", "报", "斗", "完", "类",
"八", "离", "华", "名", "确", "才", "科", "张", "信", "马",
"节", "话", "米", "整", "空", "元", "况", "今", "集", "温",
"传", "土", "许", "步", "群", "广", "石", "记", "需", "段",
"研", "界", "拉", "林", "律", "叫", "且", "究", "观", "越",
"织", "装", "影", "算", "低", "持", "音", "众", "书", "布",
"复", "容", "儿", "须", "际", "商", "非", "验", "连", "断",
"深", "难", "近", "矿", "千", "周", "委", "素", "技", "备",
"半", "办", "青", "省", "列", "习", "响", "约", "支", "般",
"史", "感", "劳", "便", "团", "往", "酸", "历", "市", "克",
"何", "除", "消", "构", "府", "称", "太", "准", "精", "值",
"号", "率", "族", "维", "划", "选", "标", "写", "存", "候",
"毛", "亲", "快", "效", "斯", "院", "查", "江", "型", "眼",
"王", "按", "格", "养", "易", "置", "派", "层", "片", "始",
"却", "专", "状", "育", "厂", "京", "识", "适", "属", "圆",
"包", "火", "住", "调", "满", "县", "局", "照", "参", "红",
"细", "引", "听", "该", "铁", "价", "严", "首", "底", "液",
"官", "德", "随", "病", "苏", "失", "尔", "死", "讲", "配",
"女", "黄", "推", "显", "谈", "罪", "神", "艺", "呢", "席",
"含", "企", "望", "密", "批", "营", "项", "防", "举", "球",
"英", "氧", "势", "告", "李", "台", "落", "木", "帮", "轮",
"破", "亚", "师", "围", "注", "远", "字", "材", "排", "供",
"河", "态", "封", "另", "施", "减", "树", "溶", "怎", "止",
"案", "言", "士", "均", "武", "固", "叶", "鱼", "波", "视",
"仅", "费", "紧", "爱", "左", "章", "早", "朝", "害", "续",
"轻", "服", "试", "食", "充", "兵", "源", "判", "护", "司",
"足", "某", "练", "差", "致", "板", "田", "降", "黑", "犯",
"负", "击", "范", "继", "兴", "似", "余", "坚", "曲", "输",
"修", "故", "城", "夫", "够", "送", "笔", "船", "占", "右",
"财", "吃", "富", "春", "职", "觉", "汉", "画", "功", "巴",
"跟", "虽", "杂", "飞", "检", "吸", "助", "升", "阳", "互",
"初", "创", "抗", "考", "投", "坏", "策", "古", "径", "换",
"未", "跑", "留", "钢", "曾", "端", "责", "站", "简", "述",
"钱", "副", "尽", "帝", "射", "草", "冲", "承", "独", "令",
"限", "阿", "宣", "环", "双", "请", "超", "微", "让", "控",
"州", "良", "轴", "找", "否", "纪", "益", "依", "优", "顶",
"础", "载", "倒", "房", "突", "坐", "粉", "敌", "略", "客",
"袁", "冷", "胜", "绝", "析", "块", "剂", "测", "丝", "协",
"诉", "念", "陈", "仍", "罗", "盐", "友", "洋", "错", "苦",
"夜", "刑", "移", "频", "逐", "靠", "混", "母", "短", "皮",
"终", "聚", "汽", "村", "云", "哪", "既", "距", "卫", "停",
"烈", "央", "察", "烧", "迅", "境", "若", "印", "洲", "刻",
"括", "激", "孔", "搞", "甚", "室", "待", "核", "校", "散",
"侵", "吧", "甲", "游", "久", "菜", "味", "旧", "模", "湖",
"货", "损", "预", "阻", "毫", "普", "稳", "乙", "妈", "植",
"息", "扩", "银", "语", "挥", "酒", "守", "拿", "序", "纸",
"医", "缺", "雨", "吗", "针", "刘", "啊", "急", "唱", "误",
"训", "愿", "审", "附", "获", "茶", "鲜", "粮", "斤", "孩",
"脱", "硫", "肥", "善", "龙", "演", "父", "渐", "血", "欢",
"械", "掌", "歌", "沙", "刚", "攻", "谓", "盾", "讨", "晚",
"粒", "乱", "燃", "矛", "乎", "杀", "药", "宁", "鲁", "贵",
"钟", "煤", "读", "班", "伯", "香", "介", "迫", "句", "丰",
"培", "握", "兰", "担", "弦", "蛋", "沉", "假", "穿", "执",
"答", "乐", "谁", "顺", "烟", "缩", "征", "脸", "喜", "松",
"脚", "困", "异", "免", "背", "星", "福", "买", "染", "井",
"概", "慢", "怕", "磁", "倍", "祖", "皇", "促", "静", "补",
"评", "翻", "肉", "践", "尼", "衣", "宽", "扬", "棉", "希",
"伤", "操", "垂", "秋", "宜", "氢", "套", "督", "振", "架",
"亮", "末", "宪", "庆", "编", "牛", "触", "映", "雷", "销",
"诗", "座", "居", "抓", "裂", "胞", "呼", "娘", "景", "威",
"绿", "晶", "厚", "盟", "衡", "鸡", "孙", "延", "危", "胶",
"屋", "乡", "临", "陆", "顾", "掉", "呀", "灯", "岁", "措",
"束", "耐", "剧", "玉", "赵", "跳", "哥", "季", "课", "凯",
"胡", "额", "款", "绍", "卷", "齐", "伟", "蒸", "殖", "永",
"宗", "苗", "川", "炉", "岩", "弱", "零", "杨", "奏", "沿",
"露", "杆", "探", "滑", "镇", "饭", "浓", "航", "怀", "赶",
"库", "夺", "伊", "灵", "税", "途", "灭", "赛", "归", "召",
"鼓", "播", "盘", "裁", "险", "康", "唯", "录", "菌", "纯",
"借", "糖", "盖", "横", "符", "私", "努", "堂", "域", "枪",
"润", "幅", "哈", "竟", "熟", "虫", "泽", "脑", "壤", "碳",
"欧", "遍", "侧", "寨", "敢", "彻", "虑", "斜", "薄", "庭",
"纳", "弹", "饲", "伸", "折", "麦", "湿", "暗", "荷", "瓦",
"塞", "床", "筑", "恶", "户", "访", "塔", "奇", "透", "梁",
"刀", "旋", "迹", "卡", "氯", "遇", "份", "毒", "泥", "退",
"洗", "摆", "灰", "彩", "卖", "耗", "夏", "择", "忙", "铜",
"献", "硬", "予", "繁", "圈", "雪", "函", "亦", "抽", "篇",
"阵", "阴", "丁", "尺", "追", "堆", "雄", "迎", "泛", "爸",
"楼", "避", "谋", "吨", "野", "猪", "旗", "累", "偏", "典",
"馆", "索", "秦", "脂", "潮", "爷", "豆", "忽", "托", "惊",
"塑", "遗", "愈", "朱", "替", "纤", "粗", "倾", "尚", "痛",
"楚", "谢", "奋", "购", "磨", "君", "池", "旁", "碎", "骨",
"监", "捕", "弟", "暴", "割", "贯", "殊", "释", "词", "亡",
"壁", "顿", "宝", "午", "尘", "闻", "揭", "炮", "残", "冬",
"桥", "妇", "警", "综", "招", "吴", "付", "浮", "遭", "徐",
"您", "摇", "谷", "赞", "箱", "隔", "订", "男", "吹", "园",
"纷", "唐", "败", "宋", "玻", "巨", "耕", "坦", "荣", "闭",
"湾", "键", "凡", "驻", "锅", "救", "恩", "剥", "凝", "碱",
"齿", "截", "炼", "麻", "纺", "禁", "废", "盛", "版", "缓",
"净", "睛", "昌", "婚", "涉", "筒", "嘴", "插", "岸", "朗",
"庄", "街", "藏", "姑", "贸", "腐", "奴", "啦", "惯", "乘",
"伙", "恢", "匀", "纱", "扎", "辩", "耳", "彪", "臣", "亿",
"璃", "抵", "脉", "秀", "萨", "俄", "网", "舞", "店", "喷",
"纵", "寸", "汗", "挂", "洪", "贺", "闪", "柬", "爆", "烯",
"津", "稻", "墙", "软", "勇", "像", "滚", "厘", "蒙", "芳",
"肯", "坡", "柱", "荡", "腿", "仪", "旅", "尾", "轧", "冰",
"贡", "登", "黎", "削", "钻", "勒", "逃", "障", "氨", "郭",
"峰", "币", "港", "伏", "轨", "亩", "毕", "擦", "莫", "刺",
"浪", "秘", "援", "株", "健", "售", "股", "岛", "甘", "泡",
"睡", "童", "铸", "汤", "阀", "休", "汇", "舍", "牧", "绕",
"炸", "哲", "磷", "绩", "朋", "淡", "尖", "启", "陷", "柴",
"呈", "徒", "颜", "泪", "稍", "忘", "泵", "蓝", "拖", "洞",
"授", "镜", "辛", "壮", "锋", "贫", "虚", "弯", "摩", "泰",
"幼", "廷", "尊", "窗", "纲", "弄", "隶", "疑", "氏", "宫",
"姐", "震", "瑞", "怪", "尤", "琴", "循", "描", "膜", "违",
"夹", "腰", "缘", "珠", "穷", "森", "枝", "竹", "沟", "催",
"绳", "忆", "邦", "剩", "幸", "浆", "栏", "拥", "牙", "贮",
"礼", "滤", "钠", "纹", "罢", "拍", "咱", "喊", "袖", "埃",
"勤", "罚", "焦", "潜", "伍", "墨", "欲", "缝", "姓", "刊",
"饱", "仿", "奖", "铝", "鬼", "丽", "跨", "默", "挖", "链",
"扫", "喝", "袋", "炭", "污", "幕", "诸", "弧", "励", "梅",
"奶", "洁", "灾", "舟", "鉴", "苯", "讼", "抱", "毁", "懂",
"寒", "智", "埔", "寄", "届", "跃", "渡", "挑", "丹", "艰",
"贝", "碰", "拔", "爹", "戴", "码", "梦", "芽", "熔", "赤",
"渔", "哭", "敬", "颗", "奔", "铅", "仲", "虎", "稀", "妹",
"乏", "珍", "申", "桌", "遵", "允", "隆", "螺", "仓", "魏",
"锐", "晓", "氮", "兼", "隐", "碍", "赫", "拨", "忠", "肃",
"缸", "牵", "抢", "博", "巧", "壳", "兄", "杜", "讯", "诚",
"碧", "祥", "柯", "页", "巡", "矩", "悲", "灌", "龄", "伦",
"票", "寻", "桂", "铺", "圣", "恐", "恰", "郑", "趣", "抬",
"荒", "腾", "贴", "柔", "滴", "猛", "阔", "辆", "妻", "填",
"撤", "储", "签", "闹", "扰", "紫", "砂", "递", "戏", "吊",
"陶", "伐", "喂", "疗", "瓶", "婆", "抚", "臂", "摸", "忍",
"虾", "蜡", "邻", "胸", "巩", "挤", "偶", "弃", "槽", "劲",
"乳", "邓", "吉", "仁", "烂", "砖", "租", "乌", "舰", "伴",
"瓜", "浅", "丙", "暂", "燥", "橡", "柳", "迷", "暖", "牌",
"秧", "胆", "详", "簧", "踏", "瓷", "谱", "呆", "宾", "糊",
"洛", "辉", "愤", "竞", "隙", "怒", "粘", "乃", "绪", "肩",
"籍", "敏", "涂", "熙", "皆", "侦", "悬", "掘", "享", "纠",
"醒", "狂", "锁", "淀", "恨", "牲", "霸", "爬", "赏", "逆",
"玩", "陵", "祝", "秒", "浙", "貌", "役", "彼", "悉", "鸭",
"趋", "凤", "晨", "畜", "辈", "秩", "卵", "署", "梯", "炎",
"滩", "棋", "驱", "筛", "峡", "冒", "啥", "寿", "译", "浸",
"泉", "帽", "迟", "硅", "疆", "贷", "漏", "稿", "冠", "嫩",
"胁", "芯", "牢", "叛", "蚀", "奥", "鸣", "岭", "羊", "凭",
"串", "塘", "绘", "酵", "融", "盆", "锡", "庙", "筹", "冻",
"辅", "摄", "袭", "筋", "拒", "僚", "旱", "钾", "鸟", "漆",
"沈", "眉", "疏", "添", "棒", "穗", "硝", "韩", "逼", "扭",
"侨", "凉", "挺", "碗", "栽", "炒", "杯", "患", "馏", "劝",
"豪", "辽", "勃", "鸿", "旦", "吏", "拜", "狗", "埋", "辊",
"掩", "饮", "搬", "骂", "辞", "勾", "扣", "估", "蒋", "绒",
"雾", "丈", "朵", "姆", "拟", "宇", "辑", "陕", "雕", "偿",
"蓄", "崇", "剪", "倡", "厅", "咬", "驶", "薯", "刷", "斥",
"番", "赋", "奉", "佛", "浇", "漫", "曼", "扇", "钙", "桃",
"扶", "仔", "返", "俗", "亏", "腔", "鞋", "棱", "覆", "框",
"悄", "叔", "撞", "骗", "勘", "旺", "沸", "孤", "吐", "孟",
"渠", "屈", "疾", "妙", "惜", "仰", "狠", "胀", "谐", "抛",
"霉", "桑", "岗", "嘛", "衰", "盗", "渗", "脏", "赖", "涌",
"甜", "曹", "阅", "肌", "哩", "厉", "烃", "纬", "毅", "昨",
"伪", "症", "煮", "叹", "钉", "搭", "茎", "笼", "酷", "偷",
"弓", "锥", "恒", "杰", "坑", "鼻", "翼", "纶", "叙", "狱",
"逮", "罐", "络", "棚", "抑", "膨", "蔬", "寺", "骤", "穆",
"冶", "枯", "册", "尸", "凸", "绅", "坯", "牺", "焰", "轰",
"欣", "晋", "瘦", "御", "锭", "锦", "丧", "旬", "锻", "垄",
"搜", "扑", "邀", "亭", "酯", "迈", "舒", "脆", "酶", "闲",
"忧", "酚", "顽", "羽", "涨", "卸", "仗", "陪", "辟", "惩",
"杭", "姚", "肚", "捉", "飘", "漂", "昆", "欺", "吾", "郎",
"烷", "汁", "呵", "饰", "萧", "雅", "邮", "迁", "燕", "撒",
"姻", "赴", "宴", "烦", "债", "帐", "斑", "铃", "旨", "醇",
"董", "饼", "雏", "姿", "拌", "傅", "腹", "妥", "揉", "贤",
"拆", "歪", "葡", "胺", "丢", "浩", "徽", "昂", "垫", "挡",
"览", "贪", "慰", "缴", "汪", "慌", "冯", "诺", "姜", "谊",
"凶", "劣", "诬", "耀", "昏", "躺", "盈", "骑", "乔", "溪",
"丛", "卢", "抹", "闷", "咨", "刮", "驾", "缆", "悟", "摘",
"铒", "掷", "颇", "幻", "柄", "惠", "惨", "佳", "仇", "腊",
"窝", "涤", "剑", "瞧", "堡", "泼", "葱", "罩", "霍", "捞",
"胎", "苍", "滨", "俩", "捅", "湘", "砍", "霞", "邵", "萄",
"疯", "淮", "遂", "熊", "粪", "烘", "宿", "档", "戈", "驳",
"嫂", "裕", "徙", "箭", "捐", "肠", "撑", "晒", "辨", "殿",
"莲", "摊", "搅", "酱", "屏", "疫", "哀", "蔡", "堵", "沫",
"皱", "畅", "叠", "阁", "莱", "敲", "辖", "钩", "痕", "坝",
"巷", "饿", "祸", "丘", "玄", "溜", "曰", "逻", "彭", "尝",
"卿", "妨", "艇", "吞", "韦", "怨", "矮", "歇" ]
</script>
        <script>WORDLISTS = typeof WORDLISTS == "undefined" ? {} : WORDLISTS;
WORDLISTS["chinese_traditional"] = [
"的", "一", "是", "在", "不", "了", "有", "和", "人", "這",
"中", "大", "為", "上", "個", "國", "我", "以", "要", "他",
"時", "來", "用", "們", "生", "到", "作", "地", "於", "出",
"就", "分", "對", "成", "會", "可", "主", "發", "年", "動",
"同", "工", "也", "能", "下", "過", "子", "說", "產", "種",
"面", "而", "方", "後", "多", "定", "行", "學", "法", "所",
"民", "得", "經", "十", "三", "之", "進", "著", "等", "部",
"度", "家", "電", "力", "裡", "如", "水", "化", "高", "自",
"二", "理", "起", "小", "物", "現", "實", "加", "量", "都",
"兩", "體", "制", "機", "當", "使", "點", "從", "業", "本",
"去", "把", "性", "好", "應", "開", "它", "合", "還", "因",
"由", "其", "些", "然", "前", "外", "天", "政", "四", "日",
"那", "社", "義", "事", "平", "形", "相", "全", "表", "間",
"樣", "與", "關", "各", "重", "新", "線", "內", "數", "正",
"心", "反", "你", "明", "看", "原", "又", "麼", "利", "比",
"或", "但", "質", "氣", "第", "向", "道", "命", "此", "變",
"條", "只", "沒", "結", "解", "問", "意", "建", "月", "公",
"無", "系", "軍", "很", "情", "者", "最", "立", "代", "想",
"已", "通", "並", "提", "直", "題", "黨", "程", "展", "五",
"果", "料", "象", "員", "革", "位", "入", "常", "文", "總",
"次", "品", "式", "活", "設", "及", "管", "特", "件", "長",
"求", "老", "頭", "基", "資", "邊", "流", "路", "級", "少",
"圖", "山", "統", "接", "知", "較", "將", "組", "見", "計",
"別", "她", "手", "角", "期", "根", "論", "運", "農", "指",
"幾", "九", "區", "強", "放", "決", "西", "被", "幹", "做",
"必", "戰", "先", "回", "則", "任", "取", "據", "處", "隊",
"南", "給", "色", "光", "門", "即", "保", "治", "北", "造",
"百", "規", "熱", "領", "七", "海", "口", "東", "導", "器",
"壓", "志", "世", "金", "增", "爭", "濟", "階", "油", "思",
"術", "極", "交", "受", "聯", "什", "認", "六", "共", "權",
"收", "證", "改", "清", "美", "再", "採", "轉", "更", "單",
"風", "切", "打", "白", "教", "速", "花", "帶", "安", "場",
"身", "車", "例", "真", "務", "具", "萬", "每", "目", "至",
"達", "走", "積", "示", "議", "聲", "報", "鬥", "完", "類",
"八", "離", "華", "名", "確", "才", "科", "張", "信", "馬",
"節", "話", "米", "整", "空", "元", "況", "今", "集", "溫",
"傳", "土", "許", "步", "群", "廣", "石", "記", "需", "段",
"研", "界", "拉", "林", "律", "叫", "且", "究", "觀", "越",
"織", "裝", "影", "算", "低", "持", "音", "眾", "書", "布",
"复", "容", "兒", "須", "際", "商", "非", "驗", "連", "斷",
"深", "難", "近", "礦", "千", "週", "委", "素", "技", "備",
"半", "辦", "青", "省", "列", "習", "響", "約", "支", "般",
"史", "感", "勞", "便", "團", "往", "酸", "歷", "市", "克",
"何", "除", "消", "構", "府", "稱", "太", "準", "精", "值",
"號", "率", "族", "維", "劃", "選", "標", "寫", "存", "候",
"毛", "親", "快", "效", "斯", "院", "查", "江", "型", "眼",
"王", "按", "格", "養", "易", "置", "派", "層", "片", "始",
"卻", "專", "狀", "育", "廠", "京", "識", "適", "屬", "圓",
"包", "火", "住", "調", "滿", "縣", "局", "照", "參", "紅",
"細", "引", "聽", "該", "鐵", "價", "嚴", "首", "底", "液",
"官", "德", "隨", "病", "蘇", "失", "爾", "死", "講", "配",
"女", "黃", "推", "顯", "談", "罪", "神", "藝", "呢", "席",
"含", "企", "望", "密", "批", "營", "項", "防", "舉", "球",
"英", "氧", "勢", "告", "李", "台", "落", "木", "幫", "輪",
"破", "亞", "師", "圍", "注", "遠", "字", "材", "排", "供",
"河", "態", "封", "另", "施", "減", "樹", "溶", "怎", "止",
"案", "言", "士", "均", "武", "固", "葉", "魚", "波", "視",
"僅", "費", "緊", "愛", "左", "章", "早", "朝", "害", "續",
"輕", "服", "試", "食", "充", "兵", "源", "判", "護", "司",
"足", "某", "練", "差", "致", "板", "田", "降", "黑", "犯",
"負", "擊", "范", "繼", "興", "似", "餘", "堅", "曲", "輸",
"修", "故", "城", "夫", "夠", "送", "筆", "船", "佔", "右",
"財", "吃", "富", "春", "職", "覺", "漢", "畫", "功", "巴",
"跟", "雖", "雜", "飛", "檢", "吸", "助", "昇", "陽", "互",
"初", "創", "抗", "考", "投", "壞", "策", "古", "徑", "換",
"未", "跑", "留", "鋼", "曾", "端", "責", "站", "簡", "述",
"錢", "副", "盡", "帝", "射", "草", "衝", "承", "獨", "令",
"限", "阿", "宣", "環", "雙", "請", "超", "微", "讓", "控",
"州", "良", "軸", "找", "否", "紀", "益", "依", "優", "頂",
"礎", "載", "倒", "房", "突", "坐", "粉", "敵", "略", "客",
"袁", "冷", "勝", "絕", "析", "塊", "劑", "測", "絲", "協",
"訴", "念", "陳", "仍", "羅", "鹽", "友", "洋", "錯", "苦",
"夜", "刑", "移", "頻", "逐", "靠", "混", "母", "短", "皮",
"終", "聚", "汽", "村", "雲", "哪", "既", "距", "衛", "停",
"烈", "央", "察", "燒", "迅", "境", "若", "印", "洲", "刻",
"括", "激", "孔", "搞", "甚", "室", "待", "核", "校", "散",
"侵", "吧", "甲", "遊", "久", "菜", "味", "舊", "模", "湖",
"貨", "損", "預", "阻", "毫", "普", "穩", "乙", "媽", "植",
"息", "擴", "銀", "語", "揮", "酒", "守", "拿", "序", "紙",
"醫", "缺", "雨", "嗎", "針", "劉", "啊", "急", "唱", "誤",
"訓", "願", "審", "附", "獲", "茶", "鮮", "糧", "斤", "孩",
"脫", "硫", "肥", "善", "龍", "演", "父", "漸", "血", "歡",
"械", "掌", "歌", "沙", "剛", "攻", "謂", "盾", "討", "晚",
"粒", "亂", "燃", "矛", "乎", "殺", "藥", "寧", "魯", "貴",
"鐘", "煤", "讀", "班", "伯", "香", "介", "迫", "句", "豐",
"培", "握", "蘭", "擔", "弦", "蛋", "沉", "假", "穿", "執",
"答", "樂", "誰", "順", "煙", "縮", "徵", "臉", "喜", "松",
"腳", "困", "異", "免", "背", "星", "福", "買", "染", "井",
"概", "慢", "怕", "磁", "倍", "祖", "皇", "促", "靜", "補",
"評", "翻", "肉", "踐", "尼", "衣", "寬", "揚", "棉", "希",
"傷", "操", "垂", "秋", "宜", "氫", "套", "督", "振", "架",
"亮", "末", "憲", "慶", "編", "牛", "觸", "映", "雷", "銷",
"詩", "座", "居", "抓", "裂", "胞", "呼", "娘", "景", "威",
"綠", "晶", "厚", "盟", "衡", "雞", "孫", "延", "危", "膠",
"屋", "鄉", "臨", "陸", "顧", "掉", "呀", "燈", "歲", "措",
"束", "耐", "劇", "玉", "趙", "跳", "哥", "季", "課", "凱",
"胡", "額", "款", "紹", "卷", "齊", "偉", "蒸", "殖", "永",
"宗", "苗", "川", "爐", "岩", "弱", "零", "楊", "奏", "沿",
"露", "桿", "探", "滑", "鎮", "飯", "濃", "航", "懷", "趕",
"庫", "奪", "伊", "靈", "稅", "途", "滅", "賽", "歸", "召",
"鼓", "播", "盤", "裁", "險", "康", "唯", "錄", "菌", "純",
"借", "糖", "蓋", "橫", "符", "私", "努", "堂", "域", "槍",
"潤", "幅", "哈", "竟", "熟", "蟲", "澤", "腦", "壤", "碳",
"歐", "遍", "側", "寨", "敢", "徹", "慮", "斜", "薄", "庭",
"納", "彈", "飼", "伸", "折", "麥", "濕", "暗", "荷", "瓦",
"塞", "床", "築", "惡", "戶", "訪", "塔", "奇", "透", "梁",
"刀", "旋", "跡", "卡", "氯", "遇", "份", "毒", "泥", "退",
"洗", "擺", "灰", "彩", "賣", "耗", "夏", "擇", "忙", "銅",
"獻", "硬", "予", "繁", "圈", "雪", "函", "亦", "抽", "篇",
"陣", "陰", "丁", "尺", "追", "堆", "雄", "迎", "泛", "爸",
"樓", "避", "謀", "噸", "野", "豬", "旗", "累", "偏", "典",
"館", "索", "秦", "脂", "潮", "爺", "豆", "忽", "托", "驚",
"塑", "遺", "愈", "朱", "替", "纖", "粗", "傾", "尚", "痛",
"楚", "謝", "奮", "購", "磨", "君", "池", "旁", "碎", "骨",
"監", "捕", "弟", "暴", "割", "貫", "殊", "釋", "詞", "亡",
"壁", "頓", "寶", "午", "塵", "聞", "揭", "炮", "殘", "冬",
"橋", "婦", "警", "綜", "招", "吳", "付", "浮", "遭", "徐",
"您", "搖", "谷", "贊", "箱", "隔", "訂", "男", "吹", "園",
"紛", "唐", "敗", "宋", "玻", "巨", "耕", "坦", "榮", "閉",
"灣", "鍵", "凡", "駐", "鍋", "救", "恩", "剝", "凝", "鹼",
"齒", "截", "煉", "麻", "紡", "禁", "廢", "盛", "版", "緩",
"淨", "睛", "昌", "婚", "涉", "筒", "嘴", "插", "岸", "朗",
"莊", "街", "藏", "姑", "貿", "腐", "奴", "啦", "慣", "乘",
"夥", "恢", "勻", "紗", "扎", "辯", "耳", "彪", "臣", "億",
"璃", "抵", "脈", "秀", "薩", "俄", "網", "舞", "店", "噴",
"縱", "寸", "汗", "掛", "洪", "賀", "閃", "柬", "爆", "烯",
"津", "稻", "牆", "軟", "勇", "像", "滾", "厘", "蒙", "芳",
"肯", "坡", "柱", "盪", "腿", "儀", "旅", "尾", "軋", "冰",
"貢", "登", "黎", "削", "鑽", "勒", "逃", "障", "氨", "郭",
"峰", "幣", "港", "伏", "軌", "畝", "畢", "擦", "莫", "刺",
"浪", "秘", "援", "株", "健", "售", "股", "島", "甘", "泡",
"睡", "童", "鑄", "湯", "閥", "休", "匯", "舍", "牧", "繞",
"炸", "哲", "磷", "績", "朋", "淡", "尖", "啟", "陷", "柴",
"呈", "徒", "顏", "淚", "稍", "忘", "泵", "藍", "拖", "洞",
"授", "鏡", "辛", "壯", "鋒", "貧", "虛", "彎", "摩", "泰",
"幼", "廷", "尊", "窗", "綱", "弄", "隸", "疑", "氏", "宮",
"姐", "震", "瑞", "怪", "尤", "琴", "循", "描", "膜", "違",
"夾", "腰", "緣", "珠", "窮", "森", "枝", "竹", "溝", "催",
"繩", "憶", "邦", "剩", "幸", "漿", "欄", "擁", "牙", "貯",
"禮", "濾", "鈉", "紋", "罷", "拍", "咱", "喊", "袖", "埃",
"勤", "罰", "焦", "潛", "伍", "墨", "欲", "縫", "姓", "刊",
"飽", "仿", "獎", "鋁", "鬼", "麗", "跨", "默", "挖", "鏈",
"掃", "喝", "袋", "炭", "污", "幕", "諸", "弧", "勵", "梅",
"奶", "潔", "災", "舟", "鑑", "苯", "訟", "抱", "毀", "懂",
"寒", "智", "埔", "寄", "屆", "躍", "渡", "挑", "丹", "艱",
"貝", "碰", "拔", "爹", "戴", "碼", "夢", "芽", "熔", "赤",
"漁", "哭", "敬", "顆", "奔", "鉛", "仲", "虎", "稀", "妹",
"乏", "珍", "申", "桌", "遵", "允", "隆", "螺", "倉", "魏",
"銳", "曉", "氮", "兼", "隱", "礙", "赫", "撥", "忠", "肅",
"缸", "牽", "搶", "博", "巧", "殼", "兄", "杜", "訊", "誠",
"碧", "祥", "柯", "頁", "巡", "矩", "悲", "灌", "齡", "倫",
"票", "尋", "桂", "鋪", "聖", "恐", "恰", "鄭", "趣", "抬",
"荒", "騰", "貼", "柔", "滴", "猛", "闊", "輛", "妻", "填",
"撤", "儲", "簽", "鬧", "擾", "紫", "砂", "遞", "戲", "吊",
"陶", "伐", "餵", "療", "瓶", "婆", "撫", "臂", "摸", "忍",
"蝦", "蠟", "鄰", "胸", "鞏", "擠", "偶", "棄", "槽", "勁",
"乳", "鄧", "吉", "仁", "爛", "磚", "租", "烏", "艦", "伴",
"瓜", "淺", "丙", "暫", "燥", "橡", "柳", "迷", "暖", "牌",
"秧", "膽", "詳", "簧", "踏", "瓷", "譜", "呆", "賓", "糊",
"洛", "輝", "憤", "競", "隙", "怒", "粘", "乃", "緒", "肩",
"籍", "敏", "塗", "熙", "皆", "偵", "懸", "掘", "享", "糾",
"醒", "狂", "鎖", "淀", "恨", "牲", "霸", "爬", "賞", "逆",
"玩", "陵", "祝", "秒", "浙", "貌", "役", "彼", "悉", "鴨",
"趨", "鳳", "晨", "畜", "輩", "秩", "卵", "署", "梯", "炎",
"灘", "棋", "驅", "篩", "峽", "冒", "啥", "壽", "譯", "浸",
"泉", "帽", "遲", "矽", "疆", "貸", "漏", "稿", "冠", "嫩",
"脅", "芯", "牢", "叛", "蝕", "奧", "鳴", "嶺", "羊", "憑",
"串", "塘", "繪", "酵", "融", "盆", "錫", "廟", "籌", "凍",
"輔", "攝", "襲", "筋", "拒", "僚", "旱", "鉀", "鳥", "漆",
"沈", "眉", "疏", "添", "棒", "穗", "硝", "韓", "逼", "扭",
"僑", "涼", "挺", "碗", "栽", "炒", "杯", "患", "餾", "勸",
"豪", "遼", "勃", "鴻", "旦", "吏", "拜", "狗", "埋", "輥",
"掩", "飲", "搬", "罵", "辭", "勾", "扣", "估", "蔣", "絨",
"霧", "丈", "朵", "姆", "擬", "宇", "輯", "陝", "雕", "償",
"蓄", "崇", "剪", "倡", "廳", "咬", "駛", "薯", "刷", "斥",
"番", "賦", "奉", "佛", "澆", "漫", "曼", "扇", "鈣", "桃",
"扶", "仔", "返", "俗", "虧", "腔", "鞋", "棱", "覆", "框",
"悄", "叔", "撞", "騙", "勘", "旺", "沸", "孤", "吐", "孟",
"渠", "屈", "疾", "妙", "惜", "仰", "狠", "脹", "諧", "拋",
"黴", "桑", "崗", "嘛", "衰", "盜", "滲", "臟", "賴", "湧",
"甜", "曹", "閱", "肌", "哩", "厲", "烴", "緯", "毅", "昨",
"偽", "症", "煮", "嘆", "釘", "搭", "莖", "籠", "酷", "偷",
"弓", "錐", "恆", "傑", "坑", "鼻", "翼", "綸", "敘", "獄",
"逮", "罐", "絡", "棚", "抑", "膨", "蔬", "寺", "驟", "穆",
"冶", "枯", "冊", "屍", "凸", "紳", "坯", "犧", "焰", "轟",
"欣", "晉", "瘦", "禦", "錠", "錦", "喪", "旬", "鍛", "壟",
"搜", "撲", "邀", "亭", "酯", "邁", "舒", "脆", "酶", "閒",
"憂", "酚", "頑", "羽", "漲", "卸", "仗", "陪", "闢", "懲",
"杭", "姚", "肚", "捉", "飄", "漂", "昆", "欺", "吾", "郎",
"烷", "汁", "呵", "飾", "蕭", "雅", "郵", "遷", "燕", "撒",
"姻", "赴", "宴", "煩", "債", "帳", "斑", "鈴", "旨", "醇",
"董", "餅", "雛", "姿", "拌", "傅", "腹", "妥", "揉", "賢",
"拆", "歪", "葡", "胺", "丟", "浩", "徽", "昂", "墊", "擋",
"覽", "貪", "慰", "繳", "汪", "慌", "馮", "諾", "姜", "誼",
"兇", "劣", "誣", "耀", "昏", "躺", "盈", "騎", "喬", "溪",
"叢", "盧", "抹", "悶", "諮", "刮", "駕", "纜", "悟", "摘",
"鉺", "擲", "頗", "幻", "柄", "惠", "慘", "佳", "仇", "臘",
"窩", "滌", "劍", "瞧", "堡", "潑", "蔥", "罩", "霍", "撈",
"胎", "蒼", "濱", "倆", "捅", "湘", "砍", "霞", "邵", "萄",
"瘋", "淮", "遂", "熊", "糞", "烘", "宿", "檔", "戈", "駁",
"嫂", "裕", "徙", "箭", "捐", "腸", "撐", "曬", "辨", "殿",
"蓮", "攤", "攪", "醬", "屏", "疫", "哀", "蔡", "堵", "沫",
"皺", "暢", "疊", "閣", "萊", "敲", "轄", "鉤", "痕", "壩",
"巷", "餓", "禍", "丘", "玄", "溜", "曰", "邏", "彭", "嘗",
"卿", "妨", "艇", "吞", "韋", "怨", "矮", "歇" ]
</script>
        <script>WORDLISTS = typeof WORDLISTS == "undefined" ? {} : WORDLISTS;
WORDLISTS["french"] = [
"abaisser", "abandon", "abdiquer", "abeille", "abolir", "aborder", "aboutir", "aboyer", "abrasif", "abreuver",
"abriter", "abroger", "abrupt", "absence", "absolu", "absurde", "abusif", "abyssal", "académie", "acajou",
"acarien", "accabler", "accepter", "acclamer", "accolade", "accroche", "accuser", "acerbe", "achat", "acheter",
"aciduler", "acier", "acompte", "acquérir", "acronyme", "acteur", "actif", "actuel", "adepte", "adéquat",
"adhésif", "adjectif", "adjuger", "admettre", "admirer", "adopter", "adorer", "adoucir", "adresse", "adroit",
"adulte", "adverbe", "aérer", "aéronef", "affaire", "affecter", "affiche", "affreux", "affubler", "agacer",
"agencer", "agile", "agiter", "agrafer", "agréable", "agrume", "aider", "aiguille", "ailier", "aimable",
"aisance", "ajouter", "ajuster", "alarmer", "alchimie", "alerte", "algèbre", "algue", "aliéner", "aliment",
"alléger", "alliage", "allouer", "allumer", "alourdir", "alpaga", "altesse", "alvéole", "amateur", "ambigu",
"ambre", "aménager", "amertume", "amidon", "amiral", "amorcer", "amour", "amovible", "amphibie", "ampleur",
"amusant", "analyse", "anaphore", "anarchie", "anatomie", "ancien", "anéantir", "angle", "angoisse", "anguleux",
"animal", "annexer", "annonce", "annuel", "anodin", "anomalie", "anonyme", "anormal", "antenne", "antidote",
"anxieux", "apaiser", "apéritif", "aplanir", "apologie", "appareil", "appeler", "apporter", "appuyer", "aquarium",
"aqueduc", "arbitre", "arbuste", "ardeur", "ardoise", "argent", "arlequin", "armature", "armement", "armoire",
"armure", "arpenter", "arracher", "arriver", "arroser", "arsenic", "artériel", "article", "aspect", "asphalte",
"aspirer", "assaut", "asservir", "assiette", "associer", "assurer", "asticot", "astre", "astuce", "atelier",
"atome", "atrium", "atroce", "attaque", "attentif", "attirer", "attraper", "aubaine", "auberge", "audace",
"audible", "augurer", "aurore", "automne", "autruche", "avaler", "avancer", "avarice", "avenir", "averse",
"aveugle", "aviateur", "avide", "avion", "aviser", "avoine", "avouer", "avril", "axial", "axiome",
"badge", "bafouer", "bagage", "baguette", "baignade", "balancer", "balcon", "baleine", "balisage", "bambin",
"bancaire", "bandage", "banlieue", "bannière", "banquier", "barbier", "baril", "baron", "barque", "barrage",
"bassin", "bastion", "bataille", "bateau", "batterie", "baudrier", "bavarder", "belette", "bélier", "belote",
"bénéfice", "berceau", "berger", "berline", "bermuda", "besace", "besogne", "bétail", "beurre", "biberon",
"bicycle", "bidule", "bijou", "bilan", "bilingue", "billard", "binaire", "biologie", "biopsie", "biotype",
"biscuit", "bison", "bistouri", "bitume", "bizarre", "blafard", "blague", "blanchir", "blessant", "blinder",
"blond", "bloquer", "blouson", "bobard", "bobine", "boire", "boiser", "bolide", "bonbon", "bondir",
"bonheur", "bonifier", "bonus", "bordure", "borne", "botte", "boucle", "boueux", "bougie", "boulon",
"bouquin", "bourse", "boussole", "boutique", "boxeur", "branche", "brasier", "brave", "brebis", "brèche",
"breuvage", "bricoler", "brigade", "brillant", "brioche", "brique", "brochure", "broder", "bronzer", "brousse",
"broyeur", "brume", "brusque", "brutal", "bruyant", "buffle", "buisson", "bulletin", "bureau", "burin",
"bustier", "butiner", "butoir", "buvable", "buvette", "cabanon", "cabine", "cachette", "cadeau", "cadre",
"caféine", "caillou", "caisson", "calculer", "calepin", "calibre", "calmer", "calomnie", "calvaire", "camarade",
"caméra", "camion", "campagne", "canal", "caneton", "canon", "cantine", "canular", "capable", "caporal",
"caprice", "capsule", "capter", "capuche", "carabine", "carbone", "caresser", "caribou", "carnage", "carotte",
"carreau", "carton", "cascade", "casier", "casque", "cassure", "causer", "caution", "cavalier", "caverne",
"caviar", "cédille", "ceinture", "céleste", "cellule", "cendrier", "censurer", "central", "cercle", "cérébral",
"cerise", "cerner", "cerveau", "cesser", "chagrin", "chaise", "chaleur", "chambre", "chance", "chapitre",
"charbon", "chasseur", "chaton", "chausson", "chavirer", "chemise", "chenille", "chéquier", "chercher", "cheval",
"chien", "chiffre", "chignon", "chimère", "chiot", "chlorure", "chocolat", "choisir", "chose", "chouette",
"chrome", "chute", "cigare", "cigogne", "cimenter", "cinéma", "cintrer", "circuler", "cirer", "cirque",
"citerne", "citoyen", "citron", "civil", "clairon", "clameur", "claquer", "classe", "clavier", "client",
"cligner", "climat", "clivage", "cloche", "clonage", "cloporte", "cobalt", "cobra", "cocasse", "cocotier",
"coder", "codifier", "coffre", "cogner", "cohésion", "coiffer", "coincer", "colère", "colibri", "colline",
"colmater", "colonel", "combat", "comédie", "commande", "compact", "concert", "conduire", "confier", "congeler",
"connoter", "consonne", "contact", "convexe", "copain", "copie", "corail", "corbeau", "cordage", "corniche",
"corpus", "correct", "cortège", "cosmique", "costume", "coton", "coude", "coupure", "courage", "couteau",
"couvrir", "coyote", "crabe", "crainte", "cravate", "crayon", "créature", "créditer", "crémeux", "creuser",
"crevette", "cribler", "crier", "cristal", "critère", "croire", "croquer", "crotale", "crucial", "cruel",
"crypter", "cubique", "cueillir", "cuillère", "cuisine", "cuivre", "culminer", "cultiver", "cumuler", "cupide",
"curatif", "curseur", "cyanure", "cycle", "cylindre", "cynique", "daigner", "damier", "danger", "danseur",
"dauphin", "débattre", "débiter", "déborder", "débrider", "débutant", "décaler", "décembre", "déchirer", "décider",
"déclarer", "décorer", "décrire", "décupler", "dédale", "déductif", "déesse", "défensif", "défiler", "défrayer",
"dégager", "dégivrer", "déglutir", "dégrafer", "déjeuner", "délice", "déloger", "demander", "demeurer", "démolir",
"dénicher", "dénouer", "dentelle", "dénuder", "départ", "dépenser", "déphaser", "déplacer", "déposer", "déranger",
"dérober", "désastre", "descente", "désert", "désigner", "désobéir", "dessiner", "destrier", "détacher", "détester",
"détourer", "détresse", "devancer", "devenir", "deviner", "devoir", "diable", "dialogue", "diamant", "dicter",
"différer", "digérer", "digital", "digne", "diluer", "dimanche", "diminuer", "dioxyde", "directif", "diriger",
"discuter", "disposer", "dissiper", "distance", "divertir", "diviser", "docile", "docteur", "dogme", "doigt",
"domaine", "domicile", "dompter", "donateur", "donjon", "donner", "dopamine", "dortoir", "dorure", "dosage",
"doseur", "dossier", "dotation", "douanier", "double", "douceur", "douter", "doyen", "dragon", "draper",
"dresser", "dribbler", "droiture", "duperie", "duplexe", "durable", "durcir", "dynastie", "éblouir", "écarter",
"écharpe", "échelle", "éclairer", "éclipse", "éclore", "écluse", "école", "économie", "écorce", "écouter",
"écraser", "écrémer", "écrivain", "écrou", "écume", "écureuil", "édifier", "éduquer", "effacer", "effectif",
"effigie", "effort", "effrayer", "effusion", "égaliser", "égarer", "éjecter", "élaborer", "élargir", "électron",
"élégant", "éléphant", "élève", "éligible", "élitisme", "éloge", "élucider", "éluder", "emballer", "embellir",
"embryon", "émeraude", "émission", "emmener", "émotion", "émouvoir", "empereur", "employer", "emporter", "emprise",
"émulsion", "encadrer", "enchère", "enclave", "encoche", "endiguer", "endosser", "endroit", "enduire", "énergie",
"enfance", "enfermer", "enfouir", "engager", "engin", "englober", "énigme", "enjamber", "enjeu", "enlever",
"ennemi", "ennuyeux", "enrichir", "enrobage", "enseigne", "entasser", "entendre", "entier", "entourer", "entraver",
"énumérer", "envahir", "enviable", "envoyer", "enzyme", "éolien", "épaissir", "épargne", "épatant", "épaule",
"épicerie", "épidémie", "épier", "épilogue", "épine", "épisode", "épitaphe", "époque", "épreuve", "éprouver",
"épuisant", "équerre", "équipe", "ériger", "érosion", "erreur", "éruption", "escalier", "espadon", "espèce",
"espiègle", "espoir", "esprit", "esquiver", "essayer", "essence", "essieu", "essorer", "estime", "estomac",
"estrade", "étagère", "étaler", "étanche", "étatique", "éteindre", "étendoir", "éternel", "éthanol", "éthique",
"ethnie", "étirer", "étoffer", "étoile", "étonnant", "étourdir", "étrange", "étroit", "étude", "euphorie",
"évaluer", "évasion", "éventail", "évidence", "éviter", "évolutif", "évoquer", "exact", "exagérer", "exaucer",
"exceller", "excitant", "exclusif", "excuse", "exécuter", "exemple", "exercer", "exhaler", "exhorter", "exigence",
"exiler", "exister", "exotique", "expédier", "explorer", "exposer", "exprimer", "exquis", "extensif", "extraire",
"exulter", "fable", "fabuleux", "facette", "facile", "facture", "faiblir", "falaise", "fameux", "famille",
"farceur", "farfelu", "farine", "farouche", "fasciner", "fatal", "fatigue", "faucon", "fautif", "faveur",
"favori", "fébrile", "féconder", "fédérer", "félin", "femme", "fémur", "fendoir", "féodal", "fermer",
"féroce", "ferveur", "festival", "feuille", "feutre", "février", "fiasco", "ficeler", "fictif", "fidèle",
"figure", "filature", "filetage", "filière", "filleul", "filmer", "filou", "filtrer", "financer", "finir",
"fiole", "firme", "fissure", "fixer", "flairer", "flamme", "flasque", "flatteur", "fléau", "flèche",
"fleur", "flexion", "flocon", "flore", "fluctuer", "fluide", "fluvial", "folie", "fonderie", "fongible",
"fontaine", "forcer", "forgeron", "formuler", "fortune", "fossile", "foudre", "fougère", "fouiller", "foulure",
"fourmi", "fragile", "fraise", "franchir", "frapper", "frayeur", "frégate", "freiner", "frelon", "frémir",
"frénésie", "frère", "friable", "friction", "frisson", "frivole", "froid", "fromage", "frontal", "frotter",
"fruit", "fugitif", "fuite", "fureur", "furieux", "furtif", "fusion", "futur", "gagner", "galaxie",
"galerie", "gambader", "garantir", "gardien", "garnir", "garrigue", "gazelle", "gazon", "géant", "gélatine",
"gélule", "gendarme", "général", "génie", "genou", "gentil", "géologie", "géomètre", "géranium", "germe",
"gestuel", "geyser", "gibier", "gicler", "girafe", "givre", "glace", "glaive", "glisser", "globe",
"gloire", "glorieux", "golfeur", "gomme", "gonfler", "gorge", "gorille", "goudron", "gouffre", "goulot",
"goupille", "gourmand", "goutte", "graduel", "graffiti", "graine", "grand", "grappin", "gratuit", "gravir",
"grenat", "griffure", "griller", "grimper", "grogner", "gronder", "grotte", "groupe", "gruger", "grutier",
"gruyère", "guépard", "guerrier", "guide", "guimauve", "guitare", "gustatif", "gymnaste", "gyrostat", "habitude",
"hachoir", "halte", "hameau", "hangar", "hanneton", "haricot", "harmonie", "harpon", "hasard", "hélium",
"hématome", "herbe", "hérisson", "hermine", "héron", "hésiter", "heureux", "hiberner", "hibou", "hilarant",
"histoire", "hiver", "homard", "hommage", "homogène", "honneur", "honorer", "honteux", "horde", "horizon",
"horloge", "hormone", "horrible", "houleux", "housse", "hublot", "huileux", "humain", "humble", "humide",
"humour", "hurler", "hydromel", "hygiène", "hymne", "hypnose", "idylle", "ignorer", "iguane", "illicite",
"illusion", "image", "imbiber", "imiter", "immense", "immobile", "immuable", "impact", "impérial", "implorer",
"imposer", "imprimer", "imputer", "incarner", "incendie", "incident", "incliner", "incolore", "indexer", "indice",
"inductif", "inédit", "ineptie", "inexact", "infini", "infliger", "informer", "infusion", "ingérer", "inhaler",
"inhiber", "injecter", "injure", "innocent", "inoculer", "inonder", "inscrire", "insecte", "insigne", "insolite",
"inspirer", "instinct", "insulter", "intact", "intense", "intime", "intrigue", "intuitif", "inutile", "invasion",
"inventer", "inviter", "invoquer", "ironique", "irradier", "irréel", "irriter", "isoler", "ivoire", "ivresse",
"jaguar", "jaillir", "jambe", "janvier", "jardin", "jauger", "jaune", "javelot", "jetable", "jeton",
"jeudi", "jeunesse", "joindre", "joncher", "jongler", "joueur", "jouissif", "journal", "jovial", "joyau",
"joyeux", "jubiler", "jugement", "junior", "jupon", "juriste", "justice", "juteux", "juvénile", "kayak",
"kimono", "kiosque", "label", "labial", "labourer", "lacérer", "lactose", "lagune", "laine", "laisser",
"laitier", "lambeau", "lamelle", "lampe", "lanceur", "langage", "lanterne", "lapin", "largeur", "larme",
"laurier", "lavabo", "lavoir", "lecture", "légal", "léger", "légume", "lessive", "lettre", "levier",
"lexique", "lézard", "liasse", "libérer", "libre", "licence", "licorne", "liège", "lièvre", "ligature",
"ligoter", "ligue", "limer", "limite", "limonade", "limpide", "linéaire", "lingot", "lionceau", "liquide",
"lisière", "lister", "lithium", "litige", "littoral", "livreur", "logique", "lointain", "loisir", "lombric",
"loterie", "louer", "lourd", "loutre", "louve", "loyal", "lubie", "lucide", "lucratif", "lueur",
"lugubre", "luisant", "lumière", "lunaire", "lundi", "luron", "lutter", "luxueux", "machine", "magasin",
"magenta", "magique", "maigre", "maillon", "maintien", "mairie", "maison", "majorer", "malaxer", "maléfice",
"malheur", "malice", "mallette", "mammouth", "mandater", "maniable", "manquant", "manteau", "manuel", "marathon",
"marbre", "marchand", "mardi", "maritime", "marqueur", "marron", "marteler", "mascotte", "massif", "matériel",
"matière", "matraque", "maudire", "maussade", "mauve", "maximal", "méchant", "méconnu", "médaille", "médecin",
"méditer", "méduse", "meilleur", "mélange", "mélodie", "membre", "mémoire", "menacer", "mener", "menhir",
"mensonge", "mentor", "mercredi", "mérite", "merle", "messager", "mesure", "métal", "météore", "méthode",
"métier", "meuble", "miauler", "microbe", "miette", "mignon", "migrer", "milieu", "million", "mimique",
"mince", "minéral", "minimal", "minorer", "minute", "miracle", "miroiter", "missile", "mixte", "mobile",
"moderne", "moelleux", "mondial", "moniteur", "monnaie", "monotone", "monstre", "montagne", "monument", "moqueur",
"morceau", "morsure", "mortier", "moteur", "motif", "mouche", "moufle", "moulin", "mousson", "mouton",
"mouvant", "multiple", "munition", "muraille", "murène", "murmure", "muscle", "muséum", "musicien", "mutation",
"muter", "mutuel", "myriade", "myrtille", "mystère", "mythique", "nageur", "nappe", "narquois", "narrer",
"natation", "nation", "nature", "naufrage", "nautique", "navire", "nébuleux", "nectar", "néfaste", "négation",
"négliger", "négocier", "neige", "nerveux", "nettoyer", "neurone", "neutron", "neveu", "niche", "nickel",
"nitrate", "niveau", "noble", "nocif", "nocturne", "noirceur", "noisette", "nomade", "nombreux", "nommer",
"normatif", "notable", "notifier", "notoire", "nourrir", "nouveau", "novateur", "novembre", "novice", "nuage",
"nuancer", "nuire", "nuisible", "numéro", "nuptial", "nuque", "nutritif", "obéir", "objectif", "obliger",
"obscur", "observer", "obstacle", "obtenir", "obturer", "occasion", "occuper", "océan", "octobre", "octroyer",
"octupler", "oculaire", "odeur", "odorant", "offenser", "officier", "offrir", "ogive", "oiseau", "oisillon",
"olfactif", "olivier", "ombrage", "omettre", "onctueux", "onduler", "onéreux", "onirique", "opale", "opaque",
"opérer", "opinion", "opportun", "opprimer", "opter", "optique", "orageux", "orange", "orbite", "ordonner",
"oreille", "organe", "orgueil", "orifice", "ornement", "orque", "ortie", "osciller", "osmose", "ossature",
"otarie", "ouragan", "ourson", "outil", "outrager", "ouvrage", "ovation", "oxyde", "oxygène", "ozone",
"paisible", "palace", "palmarès", "palourde", "palper", "panache", "panda", "pangolin", "paniquer", "panneau",
"panorama", "pantalon", "papaye", "papier", "papoter", "papyrus", "paradoxe", "parcelle", "paresse", "parfumer",
"parler", "parole", "parrain", "parsemer", "partager", "parure", "parvenir", "passion", "pastèque", "paternel",
"patience", "patron", "pavillon", "pavoiser", "payer", "paysage", "peigne", "peintre", "pelage", "pélican",
"pelle", "pelouse", "peluche", "pendule", "pénétrer", "pénible", "pensif", "pénurie", "pépite", "péplum",
"perdrix", "perforer", "période", "permuter", "perplexe", "persil", "perte", "peser", "pétale", "petit",
"pétrir", "peuple", "pharaon", "phobie", "phoque", "photon", "phrase", "physique", "piano", "pictural",
"pièce", "pierre", "pieuvre", "pilote", "pinceau", "pipette", "piquer", "pirogue", "piscine", "piston",
"pivoter", "pixel", "pizza", "placard", "plafond", "plaisir", "planer", "plaque", "plastron", "plateau",
"pleurer", "plexus", "pliage", "plomb", "plonger", "pluie", "plumage", "pochette", "poésie", "poète",
"pointe", "poirier", "poisson", "poivre", "polaire", "policier", "pollen", "polygone", "pommade", "pompier",
"ponctuel", "pondérer", "poney", "portique", "position", "posséder", "posture", "potager", "poteau", "potion",
"pouce", "poulain", "poumon", "pourpre", "poussin", "pouvoir", "prairie", "pratique", "précieux", "prédire",
"préfixe", "prélude", "prénom", "présence", "prétexte", "prévoir", "primitif", "prince", "prison", "priver",
"problème", "procéder", "prodige", "profond", "progrès", "proie", "projeter", "prologue", "promener", "propre",
"prospère", "protéger", "prouesse", "proverbe", "prudence", "pruneau", "psychose", "public", "puceron", "puiser",
"pulpe", "pulsar", "punaise", "punitif", "pupitre", "purifier", "puzzle", "pyramide", "quasar", "querelle",
"question", "quiétude", "quitter", "quotient", "racine", "raconter", "radieux", "ragondin", "raideur", "raisin",
"ralentir", "rallonge", "ramasser", "rapide", "rasage", "ratisser", "ravager", "ravin", "rayonner", "réactif",
"réagir", "réaliser", "réanimer", "recevoir", "réciter", "réclamer", "récolter", "recruter", "reculer", "recycler",
"rédiger", "redouter", "refaire", "réflexe", "réformer", "refrain", "refuge", "régalien", "région", "réglage",
"régulier", "réitérer", "rejeter", "rejouer", "relatif", "relever", "relief", "remarque", "remède", "remise",
"remonter", "remplir", "remuer", "renard", "renfort", "renifler", "renoncer", "rentrer", "renvoi", "replier",
"reporter", "reprise", "reptile", "requin", "réserve", "résineux", "résoudre", "respect", "rester", "résultat",
"rétablir", "retenir", "réticule", "retomber", "retracer", "réunion", "réussir", "revanche", "revivre", "révolte",
"révulsif", "richesse", "rideau", "rieur", "rigide", "rigoler", "rincer", "riposter", "risible", "risque",
"rituel", "rival", "rivière", "rocheux", "romance", "rompre", "ronce", "rondin", "roseau", "rosier",
"rotatif", "rotor", "rotule", "rouge", "rouille", "rouleau", "routine", "royaume", "ruban", "rubis",
"ruche", "ruelle", "rugueux", "ruiner", "ruisseau", "ruser", "rustique", "rythme", "sabler", "saboter",
"sabre", "sacoche", "safari", "sagesse", "saisir", "salade", "salive", "salon", "saluer", "samedi",
"sanction", "sanglier", "sarcasme", "sardine", "saturer", "saugrenu", "saumon", "sauter", "sauvage", "savant",
"savonner", "scalpel", "scandale", "scélérat", "scénario", "sceptre", "schéma", "science", "scinder", "score",
"scrutin", "sculpter", "séance", "sécable", "sécher", "secouer", "sécréter", "sédatif", "séduire", "seigneur",
"séjour", "sélectif", "semaine", "sembler", "semence", "séminal", "sénateur", "sensible", "sentence", "séparer",
"séquence", "serein", "sergent", "sérieux", "serrure", "sérum", "service", "sésame", "sévir", "sevrage",
"sextuple", "sidéral", "siècle", "siéger", "siffler", "sigle", "signal", "silence", "silicium", "simple",
"sincère", "sinistre", "siphon", "sirop", "sismique", "situer", "skier", "social", "socle", "sodium",
"soigneux", "soldat", "soleil", "solitude", "soluble", "sombre", "sommeil", "somnoler", "sonde", "songeur",
"sonnette", "sonore", "sorcier", "sortir", "sosie", "sottise", "soucieux", "soudure", "souffle", "soulever",
"soupape", "source", "soutirer", "souvenir", "spacieux", "spatial", "spécial", "sphère", "spiral", "stable",
"station", "sternum", "stimulus", "stipuler", "strict", "studieux", "stupeur", "styliste", "sublime", "substrat",
"subtil", "subvenir", "succès", "sucre", "suffixe", "suggérer", "suiveur", "sulfate", "superbe", "supplier",
"surface", "suricate", "surmener", "surprise", "sursaut", "survie", "suspect", "syllabe", "symbole", "symétrie",
"synapse", "syntaxe", "système", "tabac", "tablier", "tactile", "tailler", "talent", "talisman", "talonner",
"tambour", "tamiser", "tangible", "tapis", "taquiner", "tarder", "tarif", "tartine", "tasse", "tatami",
"tatouage", "taupe", "taureau", "taxer", "témoin", "temporel", "tenaille", "tendre", "teneur", "tenir",
"tension", "terminer", "terne", "terrible", "tétine", "texte", "thème", "théorie", "thérapie", "thorax",
"tibia", "tiède", "timide", "tirelire", "tiroir", "tissu", "titane", "titre", "tituber", "toboggan",
"tolérant", "tomate", "tonique", "tonneau", "toponyme", "torche", "tordre", "tornade", "torpille", "torrent",
"torse", "tortue", "totem", "toucher", "tournage", "tousser", "toxine", "traction", "trafic", "tragique",
"trahir", "train", "trancher", "travail", "trèfle", "tremper", "trésor", "treuil", "triage", "tribunal",
"tricoter", "trilogie", "triomphe", "tripler", "triturer", "trivial", "trombone", "tronc", "tropical", "troupeau",
"tuile", "tulipe", "tumulte", "tunnel", "turbine", "tuteur", "tutoyer", "tuyau", "tympan", "typhon",
"typique", "tyran", "ubuesque", "ultime", "ultrason", "unanime", "unifier", "union", "unique", "unitaire",
"univers", "uranium", "urbain", "urticant", "usage", "usine", "usuel", "usure", "utile", "utopie",
"vacarme", "vaccin", "vagabond", "vague", "vaillant", "vaincre", "vaisseau", "valable", "valise", "vallon",
"valve", "vampire", "vanille", "vapeur", "varier", "vaseux", "vassal", "vaste", "vecteur", "vedette",
"végétal", "véhicule", "veinard", "véloce", "vendredi", "vénérer", "venger", "venimeux", "ventouse", "verdure",
"vérin", "vernir", "verrou", "verser", "vertu", "veston", "vétéran", "vétuste", "vexant", "vexer",
"viaduc", "viande", "victoire", "vidange", "vidéo", "vignette", "vigueur", "vilain", "village", "vinaigre",
"violon", "vipère", "virement", "virtuose", "virus", "visage", "viseur", "vision", "visqueux", "visuel",
"vital", "vitesse", "viticole", "vitrine", "vivace", "vivipare", "vocation", "voguer", "voile", "voisin",
"voiture", "volaille", "volcan", "voltiger", "volume", "vorace", "vortex", "voter", "vouloir", "voyage",
"voyelle", "wagon", "xénon", "yacht", "zèbre", "zénith", "zeste", "zoologie"]
</script>
        <script>WORDLISTS = typeof WORDLISTS == "undefined" ? {} : WORDLISTS;
WORDLISTS["italian"] = [
"abaco", "abbaglio", "abbinato", "abete", "abisso", "abolire", "abrasivo", "abrogato", "accadere", "accenno",
"accusato", "acetone", "achille", "acido", "acqua", "acre", "acrilico", "acrobata", "acuto", "adagio",
"addebito", "addome", "adeguato", "aderire", "adipe", "adottare", "adulare", "affabile", "affetto", "affisso",
"affranto", "aforisma", "afoso", "africano", "agave", "agente", "agevole", "aggancio", "agire", "agitare",
"agonismo", "agricolo", "agrumeto", "aguzzo", "alabarda", "alato", "albatro", "alberato", "albo", "albume",
"alce", "alcolico", "alettone", "alfa", "algebra", "aliante", "alibi", "alimento", "allagato", "allegro",
"allievo", "allodola", "allusivo", "almeno", "alogeno", "alpaca", "alpestre", "altalena", "alterno", "alticcio",
"altrove", "alunno", "alveolo", "alzare", "amalgama", "amanita", "amarena", "ambito", "ambrato", "ameba",
"america", "ametista", "amico", "ammasso", "ammenda", "ammirare", "ammonito", "amore", "ampio", "ampliare",
"amuleto", "anacardo", "anagrafe", "analista", "anarchia", "anatra", "anca", "ancella", "ancora", "andare",
"andrea", "anello", "angelo", "angolare", "angusto", "anima", "annegare", "annidato", "anno", "annuncio",
"anonimo", "anticipo", "anzi", "apatico", "apertura", "apode", "apparire", "appetito", "appoggio", "approdo",
"appunto", "aprile", "arabica", "arachide", "aragosta", "araldica", "arancio", "aratura", "arazzo", "arbitro",
"archivio", "ardito", "arenile", "argento", "argine", "arguto", "aria", "armonia", "arnese", "arredato",
"arringa", "arrosto", "arsenico", "arso", "artefice", "arzillo", "asciutto", "ascolto", "asepsi", "asettico",
"asfalto", "asino", "asola", "aspirato", "aspro", "assaggio", "asse", "assoluto", "assurdo", "asta",
"astenuto", "astice", "astratto", "atavico", "ateismo", "atomico", "atono", "attesa", "attivare", "attorno",
"attrito", "attuale", "ausilio", "austria", "autista", "autonomo", "autunno", "avanzato", "avere", "avvenire",
"avviso", "avvolgere", "azione", "azoto", "azzimo", "azzurro", "babele", "baccano", "bacino", "baco",
"badessa", "badilata", "bagnato", "baita", "balcone", "baldo", "balena", "ballata", "balzano", "bambino",
"bandire", "baraonda", "barbaro", "barca", "baritono", "barlume", "barocco", "basilico", "basso", "batosta",
"battuto", "baule", "bava", "bavosa", "becco", "beffa", "belgio", "belva", "benda", "benevole",
"benigno", "benzina", "bere", "berlina", "beta", "bibita", "bici", "bidone", "bifido", "biga",
"bilancia", "bimbo", "binocolo", "biologo", "bipede", "bipolare", "birbante", "birra", "biscotto", "bisesto",
"bisnonno", "bisonte", "bisturi", "bizzarro", "blando", "blatta", "bollito", "bonifico", "bordo", "bosco",
"botanico", "bottino", "bozzolo", "braccio", "bradipo", "brama", "branca", "bravura", "bretella", "brevetto",
"brezza", "briglia", "brillante", "brindare", "broccolo", "brodo", "bronzina", "brullo", "bruno", "bubbone",
"buca", "budino", "buffone", "buio", "bulbo", "buono", "burlone", "burrasca", "bussola", "busta",
"cadetto", "caduco", "calamaro", "calcolo", "calesse", "calibro", "calmo", "caloria", "cambusa", "camerata",
"camicia", "cammino", "camola", "campale", "canapa", "candela", "cane", "canino", "canotto", "cantina",
"capace", "capello", "capitolo", "capogiro", "cappero", "capra", "capsula", "carapace", "carcassa", "cardo",
"carisma", "carovana", "carretto", "cartolina", "casaccio", "cascata", "caserma", "caso", "cassone", "castello",
"casuale", "catasta", "catena", "catrame", "cauto", "cavillo", "cedibile", "cedrata", "cefalo", "celebre",
"cellulare", "cena", "cenone", "centesimo", "ceramica", "cercare", "certo", "cerume", "cervello", "cesoia",
"cespo", "ceto", "chela", "chiaro", "chicca", "chiedere", "chimera", "china", "chirurgo", "chitarra",
"ciao", "ciclismo", "cifrare", "cigno", "cilindro", "ciottolo", "circa", "cirrosi", "citrico", "cittadino",
"ciuffo", "civetta", "civile", "classico", "clinica", "cloro", "cocco", "codardo", "codice", "coerente",
"cognome", "collare", "colmato", "colore", "colposo", "coltivato", "colza", "coma", "cometa", "commando",
"comodo", "computer", "comune", "conciso", "condurre", "conferma", "congelare", "coniuge", "connesso", "conoscere",
"consumo", "continuo", "convegno", "coperto", "copione", "coppia", "copricapo", "corazza", "cordata", "coricato",
"cornice", "corolla", "corpo", "corredo", "corsia", "cortese", "cosmico", "costante", "cottura", "covato",
"cratere", "cravatta", "creato", "credere", "cremoso", "crescita", "creta", "criceto", "crinale", "crisi",
"critico", "croce", "cronaca", "crostata", "cruciale", "crusca", "cucire", "cuculo", "cugino", "cullato",
"cupola", "curatore", "cursore", "curvo", "cuscino", "custode", "dado", "daino", "dalmata", "damerino",
"daniela", "dannoso", "danzare", "datato", "davanti", "davvero", "debutto", "decennio", "deciso", "declino",
"decollo", "decreto", "dedicato", "definito", "deforme", "degno", "delegare", "delfino", "delirio", "delta",
"demenza", "denotato", "dentro", "deposito", "derapata", "derivare", "deroga", "descritto", "deserto", "desiderio",
"desumere", "detersivo", "devoto", "diametro", "dicembre", "diedro", "difeso", "diffuso", "digerire", "digitale",
"diluvio", "dinamico", "dinnanzi", "dipinto", "diploma", "dipolo", "diradare", "dire", "dirotto", "dirupo",
"disagio", "discreto", "disfare", "disgelo", "disposto", "distanza", "disumano", "dito", "divano", "divelto",
"dividere", "divorato", "doblone", "docente", "doganale", "dogma", "dolce", "domato", "domenica", "dominare",
"dondolo", "dono", "dormire", "dote", "dottore", "dovuto", "dozzina", "drago", "druido", "dubbio",
"dubitare", "ducale", "duna", "duomo", "duplice", "duraturo", "ebano", "eccesso", "ecco", "eclissi",
"economia", "edera", "edicola", "edile", "editoria", "educare", "egemonia", "egli", "egoismo", "egregio",
"elaborato", "elargire", "elegante", "elencato", "eletto", "elevare", "elfico", "elica", "elmo", "elsa",
"eluso", "emanato", "emblema", "emesso", "emiro", "emotivo", "emozione", "empirico", "emulo", "endemico",
"enduro", "energia", "enfasi", "enoteca", "entrare", "enzima", "epatite", "epilogo", "episodio", "epocale",
"eppure", "equatore", "erario", "erba", "erboso", "erede", "eremita", "erigere", "ermetico", "eroe",
"erosivo", "errante", "esagono", "esame", "esanime", "esaudire", "esca", "esempio", "esercito", "esibito",
"esigente", "esistere", "esito", "esofago", "esortato", "esoso", "espanso", "espresso", "essenza", "esso",
"esteso", "estimare", "estonia", "estroso", "esultare", "etilico", "etnico", "etrusco", "etto", "euclideo",
"europa", "evaso", "evidenza", "evitato", "evoluto", "evviva", "fabbrica", "faccenda", "fachiro", "falco",
"famiglia", "fanale", "fanfara", "fango", "fantasma", "fare", "farfalla", "farinoso", "farmaco", "fascia",
"fastoso", "fasullo", "faticare", "fato", "favoloso", "febbre", "fecola", "fede", "fegato", "felpa",
"feltro", "femmina", "fendere", "fenomeno", "fermento", "ferro", "fertile", "fessura", "festivo", "fetta",
"feudo", "fiaba", "fiducia", "fifa", "figurato", "filo", "finanza", "finestra", "finire", "fiore",
"fiscale", "fisico", "fiume", "flacone", "flamenco", "flebo", "flemma", "florido", "fluente", "fluoro",
"fobico", "focaccia", "focoso", "foderato", "foglio", "folata", "folclore", "folgore", "fondente", "fonetico",
"fonia", "fontana", "forbito", "forchetta", "foresta", "formica", "fornaio", "foro", "fortezza", "forzare",
"fosfato", "fosso", "fracasso", "frana", "frassino", "fratello", "freccetta", "frenata", "fresco", "frigo",
"frollino", "fronde", "frugale", "frutta", "fucilata", "fucsia", "fuggente", "fulmine", "fulvo", "fumante",
"fumetto", "fumoso", "fune", "funzione", "fuoco", "furbo", "furgone", "furore", "fuso", "futile",
"gabbiano", "gaffe", "galateo", "gallina", "galoppo", "gambero", "gamma", "garanzia", "garbo", "garofano",
"garzone", "gasdotto", "gasolio", "gastrico", "gatto", "gaudio", "gazebo", "gazzella", "geco", "gelatina",
"gelso", "gemello", "gemmato", "gene", "genitore", "gennaio", "genotipo", "gergo", "ghepardo", "ghiaccio",
"ghisa", "giallo", "gilda", "ginepro", "giocare", "gioiello", "giorno", "giove", "girato", "girone",
"gittata", "giudizio", "giurato", "giusto", "globulo", "glutine", "gnomo", "gobba", "golf", "gomito",
"gommone", "gonfio", "gonna", "governo", "gracile", "grado", "grafico", "grammo", "grande", "grattare",
"gravoso", "grazia", "greca", "gregge", "grifone", "grigio", "grinza", "grotta", "gruppo", "guadagno",
"guaio", "guanto", "guardare", "gufo", "guidare", "ibernato", "icona", "identico", "idillio", "idolo",
"idra", "idrico", "idrogeno", "igiene", "ignaro", "ignorato", "ilare", "illeso", "illogico", "illudere",
"imballo", "imbevuto", "imbocco", "imbuto", "immane", "immerso", "immolato", "impacco", "impeto", "impiego",
"importo", "impronta", "inalare", "inarcare", "inattivo", "incanto", "incendio", "inchino", "incisivo", "incluso",
"incontro", "incrocio", "incubo", "indagine", "india", "indole", "inedito", "infatti", "infilare", "inflitto",
"ingaggio", "ingegno", "inglese", "ingordo", "ingrosso", "innesco", "inodore", "inoltrare", "inondato", "insano",
"insetto", "insieme", "insonnia", "insulina", "intasato", "intero", "intonaco", "intuito", "inumidire", "invalido",
"invece", "invito", "iperbole", "ipnotico", "ipotesi", "ippica", "iride", "irlanda", "ironico", "irrigato",
"irrorare", "isolato", "isotopo", "isterico", "istituto", "istrice", "italia", "iterare", "labbro", "labirinto",
"lacca", "lacerato", "lacrima", "lacuna", "laddove", "lago", "lampo", "lancetta", "lanterna", "lardoso",
"larga", "laringe", "lastra", "latenza", "latino", "lattuga", "lavagna", "lavoro", "legale", "leggero",
"lembo", "lentezza", "lenza", "leone", "lepre", "lesivo", "lessato", "lesto", "letterale", "leva",
"levigato", "libero", "lido", "lievito", "lilla", "limatura", "limitare", "limpido", "lineare", "lingua",
"liquido", "lira", "lirica", "lisca", "lite", "litigio", "livrea", "locanda", "lode", "logica",
"lombare", "londra", "longevo", "loquace", "lorenzo", "loto", "lotteria", "luce", "lucidato", "lumaca",
"luminoso", "lungo", "lupo", "luppolo", "lusinga", "lusso", "lutto", "macabro", "macchina", "macero",
"macinato", "madama", "magico", "maglia", "magnete", "magro", "maiolica", "malafede", "malgrado", "malinteso",
"malsano", "malto", "malumore", "mana", "mancia", "mandorla", "mangiare", "manifesto", "mannaro", "manovra",
"mansarda", "mantide", "manubrio", "mappa", "maratona", "marcire", "maretta", "marmo", "marsupio", "maschera",
"massaia", "mastino", "materasso", "matricola", "mattone", "maturo", "mazurca", "meandro", "meccanico", "mecenate",
"medesimo", "meditare", "mega", "melassa", "melis", "melodia", "meninge", "meno", "mensola", "mercurio",
"merenda", "merlo", "meschino", "mese", "messere", "mestolo", "metallo", "metodo", "mettere", "miagolare",
"mica", "micelio", "michele", "microbo", "midollo", "miele", "migliore", "milano", "milite", "mimosa",
"minerale", "mini", "minore", "mirino", "mirtillo", "miscela", "missiva", "misto", "misurare", "mitezza",
"mitigare", "mitra", "mittente", "mnemonico", "modello", "modifica", "modulo", "mogano", "mogio", "mole",
"molosso", "monastero", "monco", "mondina", "monetario", "monile", "monotono", "monsone", "montato", "monviso",
"mora", "mordere", "morsicato", "mostro", "motivato", "motosega", "motto", "movenza", "movimento", "mozzo",
"mucca", "mucosa", "muffa", "mughetto", "mugnaio", "mulatto", "mulinello", "multiplo", "mummia", "munto",
"muovere", "murale", "musa", "muscolo", "musica", "mutevole", "muto", "nababbo", "nafta", "nanometro",
"narciso", "narice", "narrato", "nascere", "nastrare", "naturale", "nautica", "naviglio", "nebulosa", "necrosi",
"negativo", "negozio", "nemmeno", "neofita", "neretto", "nervo", "nessuno", "nettuno", "neutrale", "neve",
"nevrotico", "nicchia", "ninfa", "nitido", "nobile", "nocivo", "nodo", "nome", "nomina", "nordico",
"normale", "norvegese", "nostrano", "notare", "notizia", "notturno", "novella", "nucleo", "nulla", "numero",
"nuovo", "nutrire", "nuvola", "nuziale", "oasi", "obbedire", "obbligo", "obelisco", "oblio", "obolo",
"obsoleto", "occasione", "occhio", "occidente", "occorrere", "occultare", "ocra", "oculato", "odierno", "odorare",
"offerta", "offrire", "offuscato", "oggetto", "oggi", "ognuno", "olandese", "olfatto", "oliato", "oliva",
"ologramma", "oltre", "omaggio", "ombelico", "ombra", "omega", "omissione", "ondoso", "onere", "onice",
"onnivoro", "onorevole", "onta", "operato", "opinione", "opposto", "oracolo", "orafo", "ordine", "orecchino",
"orefice", "orfano", "organico", "origine", "orizzonte", "orma", "ormeggio", "ornativo", "orologio", "orrendo",
"orribile", "ortensia", "ortica", "orzata", "orzo", "osare", "oscurare", "osmosi", "ospedale", "ospite",
"ossa", "ossidare", "ostacolo", "oste", "otite", "otre", "ottagono", "ottimo", "ottobre", "ovale",
"ovest", "ovino", "oviparo", "ovocito", "ovunque", "ovviare", "ozio", "pacchetto", "pace", "pacifico",
"padella", "padrone", "paese", "paga", "pagina", "palazzina", "palesare", "pallido", "palo", "palude",
"pandoro", "pannello", "paolo", "paonazzo", "paprica", "parabola", "parcella", "parere", "pargolo", "pari",
"parlato", "parola", "partire", "parvenza", "parziale", "passivo", "pasticca", "patacca", "patologia", "pattume",
"pavone", "peccato", "pedalare", "pedonale", "peggio", "peloso", "penare", "pendice", "penisola", "pennuto",
"penombra", "pensare", "pentola", "pepe", "pepita", "perbene", "percorso", "perdonato", "perforare", "pergamena",
"periodo", "permesso", "perno", "perplesso", "persuaso", "pertugio", "pervaso", "pesatore", "pesista", "peso",
"pestifero", "petalo", "pettine", "petulante", "pezzo", "piacere", "pianta", "piattino", "piccino", "picozza",
"piega", "pietra", "piffero", "pigiama", "pigolio", "pigro", "pila", "pilifero", "pillola", "pilota",
"pimpante", "pineta", "pinna", "pinolo", "pioggia", "piombo", "piramide", "piretico", "pirite", "pirolisi",
"pitone", "pizzico", "placebo", "planare", "plasma", "platano", "plenario", "pochezza", "poderoso", "podismo",
"poesia", "poggiare", "polenta", "poligono", "pollice", "polmonite", "polpetta", "polso", "poltrona", "polvere",
"pomice", "pomodoro", "ponte", "popoloso", "porfido", "poroso", "porpora", "porre", "portata", "posa",
"positivo", "possesso", "postulato", "potassio", "potere", "pranzo", "prassi", "pratica", "precluso", "predica",
"prefisso", "pregiato", "prelievo", "premere", "prenotare", "preparato", "presenza", "pretesto", "prevalso", "prima",
"principe", "privato", "problema", "procura", "produrre", "profumo", "progetto", "prolunga", "promessa", "pronome",
"proposta", "proroga", "proteso", "prova", "prudente", "prugna", "prurito", "psiche", "pubblico", "pudica",
"pugilato", "pugno", "pulce", "pulito", "pulsante", "puntare", "pupazzo", "pupilla", "puro", "quadro",
"qualcosa", "quasi", "querela", "quota", "raccolto", "raddoppio", "radicale", "radunato", "raffica", "ragazzo",
"ragione", "ragno", "ramarro", "ramingo", "ramo", "randagio", "rantolare", "rapato", "rapina", "rappreso",
"rasatura", "raschiato", "rasente", "rassegna", "rastrello", "rata", "ravveduto", "reale", "recepire", "recinto",
"recluta", "recondito", "recupero", "reddito", "redimere", "regalato", "registro", "regola", "regresso", "relazione",
"remare", "remoto", "renna", "replica", "reprimere", "reputare", "resa", "residente", "responso", "restauro",
"rete", "retina", "retorica", "rettifica", "revocato", "riassunto", "ribadire", "ribelle", "ribrezzo", "ricarica",
"ricco", "ricevere", "riciclato", "ricordo", "ricreduto", "ridicolo", "ridurre", "rifasare", "riflesso", "riforma",
"rifugio", "rigare", "rigettato", "righello", "rilassato", "rilevato", "rimanere", "rimbalzo", "rimedio", "rimorchio",
"rinascita", "rincaro", "rinforzo", "rinnovo", "rinomato", "rinsavito", "rintocco", "rinuncia", "rinvenire", "riparato",
"ripetuto", "ripieno", "riportare", "ripresa", "ripulire", "risata", "rischio", "riserva", "risibile", "riso",
"rispetto", "ristoro", "risultato", "risvolto", "ritardo", "ritegno", "ritmico", "ritrovo", "riunione", "riva",
"riverso", "rivincita", "rivolto", "rizoma", "roba", "robotico", "robusto", "roccia", "roco", "rodaggio",
"rodere", "roditore", "rogito", "rollio", "romantico", "rompere", "ronzio", "rosolare", "rospo", "rotante",
"rotondo", "rotula", "rovescio", "rubizzo", "rubrica", "ruga", "rullino", "rumine", "rumoroso", "ruolo",
"rupe", "russare", "rustico", "sabato", "sabbiare", "sabotato", "sagoma", "salasso", "saldatura", "salgemma",
"salivare", "salmone", "salone", "saltare", "saluto", "salvo", "sapere", "sapido", "saporito", "saraceno",
"sarcasmo", "sarto", "sassoso", "satellite", "satira", "satollo", "saturno", "savana", "savio", "saziato",
"sbadiglio", "sbalzo", "sbancato", "sbarra", "sbattere", "sbavare", "sbendare", "sbirciare", "sbloccato", "sbocciato",
"sbrinare", "sbruffone", "sbuffare", "scabroso", "scadenza", "scala", "scambiare", "scandalo", "scapola", "scarso",
"scatenare", "scavato", "scelto", "scenico", "scettro", "scheda", "schiena", "sciarpa", "scienza", "scindere",
"scippo", "sciroppo", "scivolo", "sclerare", "scodella", "scolpito", "scomparto", "sconforto", "scoprire", "scorta",
"scossone", "scozzese", "scriba", "scrollare", "scrutinio", "scuderia", "scultore", "scuola", "scuro", "scusare",
"sdebitare", "sdoganare", "seccatura", "secondo", "sedano", "seggiola", "segnalato", "segregato", "seguito", "selciato",
"selettivo", "sella", "selvaggio", "semaforo", "sembrare", "seme", "seminato", "sempre", "senso", "sentire",
"sepolto", "sequenza", "serata", "serbato", "sereno", "serio", "serpente", "serraglio", "servire", "sestina",
"setola", "settimana", "sfacelo", "sfaldare", "sfamato", "sfarzoso", "sfaticato", "sfera", "sfida", "sfilato",
"sfinge", "sfocato", "sfoderare", "sfogo", "sfoltire", "sforzato", "sfratto", "sfruttato", "sfuggito", "sfumare",
"sfuso", "sgabello", "sgarbato", "sgonfiare", "sgorbio", "sgrassato", "sguardo", "sibilo", "siccome", "sierra",
"sigla", "signore", "silenzio", "sillaba", "simbolo", "simpatico", "simulato", "sinfonia", "singolo", "sinistro",
"sino", "sintesi", "sinusoide", "sipario", "sisma", "sistole", "situato", "slitta", "slogatura", "sloveno",
"smarrito", "smemorato", "smentito", "smeraldo", "smilzo", "smontare", "smottato", "smussato", "snellire", "snervato",
"snodo", "sobbalzo", "sobrio", "soccorso", "sociale", "sodale", "soffitto", "sogno", "soldato", "solenne",
"solido", "sollazzo", "solo", "solubile", "solvente", "somatico", "somma", "sonda", "sonetto", "sonnifero",
"sopire", "soppeso", "sopra", "sorgere", "sorpasso", "sorriso", "sorso", "sorteggio", "sorvolato", "sospiro",
"sosta", "sottile", "spada", "spalla", "spargere", "spatola", "spavento", "spazzola", "specie", "spedire",
"spegnere", "spelatura", "speranza", "spessore", "spettrale", "spezzato", "spia", "spigoloso", "spillato", "spinoso",
"spirale", "splendido", "sportivo", "sposo", "spranga", "sprecare", "spronato", "spruzzo", "spuntino", "squillo",
"sradicare", "srotolato", "stabile", "stacco", "staffa", "stagnare", "stampato", "stantio", "starnuto", "stasera",
"statuto", "stelo", "steppa", "sterzo", "stiletto", "stima", "stirpe", "stivale", "stizzoso", "stonato",
"storico", "strappo", "stregato", "stridulo", "strozzare", "strutto", "stuccare", "stufo", "stupendo", "subentro",
"succoso", "sudore", "suggerito", "sugo", "sultano", "suonare", "superbo", "supporto", "surgelato", "surrogato",
"sussurro", "sutura", "svagare", "svedese", "sveglio", "svelare", "svenuto", "svezia", "sviluppo", "svista",
"svizzera", "svolta", "svuotare", "tabacco", "tabulato", "tacciare", "taciturno", "tale", "talismano", "tampone",
"tannino", "tara", "tardivo", "targato", "tariffa", "tarpare", "tartaruga", "tasto", "tattico", "taverna",
"tavolata", "tazza", "teca", "tecnico", "telefono", "temerario", "tempo", "temuto", "tendone", "tenero",
"tensione", "tentacolo", "teorema", "terme", "terrazzo", "terzetto", "tesi", "tesserato", "testato", "tetro",
"tettoia", "tifare", "tigella", "timbro", "tinto", "tipico", "tipografo", "tiraggio", "tiro", "titanio",
"titolo", "titubante", "tizio", "tizzone", "toccare", "tollerare", "tolto", "tombola", "tomo", "tonfo",
"tonsilla", "topazio", "topologia", "toppa", "torba", "tornare", "torrone", "tortora", "toscano", "tossire",
"tostatura", "totano", "trabocco", "trachea", "trafila", "tragedia", "tralcio", "tramonto", "transito", "trapano",
"trarre", "trasloco", "trattato", "trave", "treccia", "tremolio", "trespolo", "tributo", "tricheco", "trifoglio",
"trillo", "trincea", "trio", "tristezza", "triturato", "trivella", "tromba", "trono", "troppo", "trottola",
"trovare", "truccato", "tubatura", "tuffato", "tulipano", "tumulto", "tunisia", "turbare", "turchino", "tuta",
"tutela", "ubicato", "uccello", "uccisore", "udire", "uditivo", "uffa", "ufficio", "uguale", "ulisse",
"ultimato", "umano", "umile", "umorismo", "uncinetto", "ungere", "ungherese", "unicorno", "unificato", "unisono",
"unitario", "unte", "uovo", "upupa", "uragano", "urgenza", "urlo", "usanza", "usato", "uscito",
"usignolo", "usuraio", "utensile", "utilizzo", "utopia", "vacante", "vaccinato", "vagabondo", "vagliato", "valanga",
"valgo", "valico", "valletta", "valoroso", "valutare", "valvola", "vampata", "vangare", "vanitoso", "vano",
"vantaggio", "vanvera", "vapore", "varano", "varcato", "variante", "vasca", "vedetta", "vedova", "veduto",
"vegetale", "veicolo", "velcro", "velina", "velluto", "veloce", "venato", "vendemmia", "vento", "verace",
"verbale", "vergogna", "verifica", "vero", "verruca", "verticale", "vescica", "vessillo", "vestale", "veterano",
"vetrina", "vetusto", "viandante", "vibrante", "vicenda", "vichingo", "vicinanza", "vidimare", "vigilia", "vigneto",
"vigore", "vile", "villano", "vimini", "vincitore", "viola", "vipera", "virgola", "virologo", "virulento",
"viscoso", "visione", "vispo", "vissuto", "visura", "vita", "vitello", "vittima", "vivanda", "vivido",
"viziare", "voce", "voga", "volatile", "volere", "volpe", "voragine", "vulcano", "zampogna", "zanna",
"zappato", "zattera", "zavorra", "zefiro", "zelante", "zelo", "zenzero", "zerbino", "zibetto", "zinco",
"zircone", "zitto", "zolla", "zotico", "zucchero", "zufolo", "zulu", "zuppa"]
</script>
        <script>WORDLISTS = typeof WORDLISTS == "undefined" ? {} : WORDLISTS;
WORDLISTS["korean"] = [
  "가격",
  "가끔",
  "가난",
  "가능",
  "가득",
  "가르침",
  "가뭄",
  "가방",
  "가상",
  "가슴",
  "가운데",
  "가을",
  "가이드",
  "가입",
  "가장",
  "가정",
  "가족",
  "가죽",
  "각오",
  "각자",
  "간격",
  "간부",
  "간섭",
  "간장",
  "간접",
  "간판",
  "갈등",
  "갈비",
  "갈색",
  "갈증",
  "감각",
  "감기",
  "감소",
  "감수성",
  "감자",
  "감정",
  "갑자기",
  "강남",
  "강당",
  "강도",
  "강력히",
  "강변",
  "강북",
  "강사",
  "강수량",
  "강아지",
  "강원도",
  "강의",
  "강제",
  "강조",
  "같이",
  "개구리",
  "개나리",
  "개방",
  "개별",
  "개선",
  "개성",
  "개인",
  "객관적",
  "거실",
  "거액",
  "거울",
  "거짓",
  "거품",
  "걱정",
  "건강",
  "건물",
  "건설",
  "건조",
  "건축",
  "걸음",
  "검사",
  "검토",
  "게시판",
  "게임",
  "겨울",
  "견해",
  "결과",
  "결국",
  "결론",
  "결석",
  "결승",
  "결심",
  "결정",
  "결혼",
  "경계",
  "경고",
  "경기",
  "경력",
  "경복궁",
  "경비",
  "경상도",
  "경영",
  "경우",
  "경쟁",
  "경제",
  "경주",
  "경찰",
  "경치",
  "경향",
  "경험",
  "계곡",
  "계단",
  "계란",
  "계산",
  "계속",
  "계약",
  "계절",
  "계층",
  "계획",
  "고객",
  "고구려",
  "고궁",
  "고급",
  "고등학생",
  "고무신",
  "고민",
  "고양이",
  "고장",
  "고전",
  "고집",
  "고춧가루",
  "고통",
  "고향",
  "곡식",
  "골목",
  "골짜기",
  "골프",
  "공간",
  "공개",
  "공격",
  "공군",
  "공급",
  "공기",
  "공동",
  "공무원",
  "공부",
  "공사",
  "공식",
  "공업",
  "공연",
  "공원",
  "공장",
  "공짜",
  "공책",
  "공통",
  "공포",
  "공항",
  "공휴일",
  "과목",
  "과일",
  "과장",
  "과정",
  "과학",
  "관객",
  "관계",
  "관광",
  "관념",
  "관람",
  "관련",
  "관리",
  "관습",
  "관심",
  "관점",
  "관찰",
  "광경",
  "광고",
  "광장",
  "광주",
  "괴로움",
  "굉장히",
  "교과서",
  "교문",
  "교복",
  "교실",
  "교양",
  "교육",
  "교장",
  "교직",
  "교통",
  "교환",
  "교훈",
  "구경",
  "구름",
  "구멍",
  "구별",
  "구분",
  "구석",
  "구성",
  "구속",
  "구역",
  "구입",
  "구청",
  "구체적",
  "국가",
  "국기",
  "국내",
  "국립",
  "국물",
  "국민",
  "국수",
  "국어",
  "국왕",
  "국적",
  "국제",
  "국회",
  "군대",
  "군사",
  "군인",
  "궁극적",
  "권리",
  "권위",
  "권투",
  "귀국",
  "귀신",
  "규정",
  "규칙",
  "균형",
  "그날",
  "그냥",
  "그늘",
  "그러나",
  "그룹",
  "그릇",
  "그림",
  "그제서야",
  "그토록",
  "극복",
  "극히",
  "근거",
  "근교",
  "근래",
  "근로",
  "근무",
  "근본",
  "근원",
  "근육",
  "근처",
  "글씨",
  "글자",
  "금강산",
  "금고",
  "금년",
  "금메달",
  "금액",
  "금연",
  "금요일",
  "금지",
  "긍정적",
  "기간",
  "기관",
  "기념",
  "기능",
  "기독교",
  "기둥",
  "기록",
  "기름",
  "기법",
  "기본",
  "기분",
  "기쁨",
  "기숙사",
  "기술",
  "기억",
  "기업",
  "기온",
  "기운",
  "기원",
  "기적",
  "기준",
  "기침",
  "기혼",
  "기획",
  "긴급",
  "긴장",
  "길이",
  "김밥",
  "김치",
  "김포공항",
  "깍두기",
  "깜빡",
  "깨달음",
  "깨소금",
  "껍질",
  "꼭대기",
  "꽃잎",
  "나들이",
  "나란히",
  "나머지",
  "나물",
  "나침반",
  "나흘",
  "낙엽",
  "난방",
  "날개",
  "날씨",
  "날짜",
  "남녀",
  "남대문",
  "남매",
  "남산",
  "남자",
  "남편",
  "남학생",
  "낭비",
  "낱말",
  "내년",
  "내용",
  "내일",
  "냄비",
  "냄새",
  "냇물",
  "냉동",
  "냉면",
  "냉방",
  "냉장고",
  "넥타이",
  "넷째",
  "노동",
  "노란색",
  "노력",
  "노인",
  "녹음",
  "녹차",
  "녹화",
  "논리",
  "논문",
  "논쟁",
  "놀이",
  "농구",
  "농담",
  "농민",
  "농부",
  "농업",
  "농장",
  "농촌",
  "높이",
  "눈동자",
  "눈물",
  "눈썹",
  "뉴욕",
  "느낌",
  "늑대",
  "능동적",
  "능력",
  "다방",
  "다양성",
  "다음",
  "다이어트",
  "다행",
  "단계",
  "단골",
  "단독",
  "단맛",
  "단순",
  "단어",
  "단위",
  "단점",
  "단체",
  "단추",
  "단편",
  "단풍",
  "달걀",
  "달러",
  "달력",
  "달리",
  "닭고기",
  "담당",
  "담배",
  "담요",
  "담임",
  "답변",
  "답장",
  "당근",
  "당분간",
  "당연히",
  "당장",
  "대규모",
  "대낮",
  "대단히",
  "대답",
  "대도시",
  "대략",
  "대량",
  "대륙",
  "대문",
  "대부분",
  "대신",
  "대응",
  "대장",
  "대전",
  "대접",
  "대중",
  "대책",
  "대출",
  "대충",
  "대통령",
  "대학",
  "대한민국",
  "대합실",
  "대형",
  "덩어리",
  "데이트",
  "도대체",
  "도덕",
  "도둑",
  "도망",
  "도서관",
  "도심",
  "도움",
  "도입",
  "도자기",
  "도저히",
  "도전",
  "도중",
  "도착",
  "독감",
  "독립",
  "독서",
  "독일",
  "독창적",
  "동화책",
  "뒷모습",
  "뒷산",
  "딸아이",
  "마누라",
  "마늘",
  "마당",
  "마라톤",
  "마련",
  "마무리",
  "마사지",
  "마약",
  "마요네즈",
  "마을",
  "마음",
  "마이크",
  "마중",
  "마지막",
  "마찬가지",
  "마찰",
  "마흔",
  "막걸리",
  "막내",
  "막상",
  "만남",
  "만두",
  "만세",
  "만약",
  "만일",
  "만점",
  "만족",
  "만화",
  "많이",
  "말기",
  "말씀",
  "말투",
  "맘대로",
  "망원경",
  "매년",
  "매달",
  "매력",
  "매번",
  "매스컴",
  "매일",
  "매장",
  "맥주",
  "먹이",
  "먼저",
  "먼지",
  "멀리",
  "메일",
  "며느리",
  "며칠",
  "면담",
  "멸치",
  "명단",
  "명령",
  "명예",
  "명의",
  "명절",
  "명칭",
  "명함",
  "모금",
  "모니터",
  "모델",
  "모든",
  "모범",
  "모습",
  "모양",
  "모임",
  "모조리",
  "모집",
  "모퉁이",
  "목걸이",
  "목록",
  "목사",
  "목소리",
  "목숨",
  "목적",
  "목표",
  "몰래",
  "몸매",
  "몸무게",
  "몸살",
  "몸속",
  "몸짓",
  "몸통",
  "몹시",
  "무관심",
  "무궁화",
  "무더위",
  "무덤",
  "무릎",
  "무슨",
  "무엇",
  "무역",
  "무용",
  "무조건",
  "무지개",
  "무척",
  "문구",
  "문득",
  "문법",
  "문서",
  "문제",
  "문학",
  "문화",
  "물가",
  "물건",
  "물결",
  "물고기",
  "물론",
  "물리학",
  "물음",
  "물질",
  "물체",
  "미국",
  "미디어",
  "미사일",
  "미술",
  "미역",
  "미용실",
  "미움",
  "미인",
  "미팅",
  "미혼",
  "민간",
  "민족",
  "민주",
  "믿음",
  "밀가루",
  "밀리미터",
  "밑바닥",
  "바가지",
  "바구니",
  "바나나",
  "바늘",
  "바닥",
  "바닷가",
  "바람",
  "바이러스",
  "바탕",
  "박물관",
  "박사",
  "박수",
  "반대",
  "반드시",
  "반말",
  "반발",
  "반성",
  "반응",
  "반장",
  "반죽",
  "반지",
  "반찬",
  "받침",
  "발가락",
  "발걸음",
  "발견",
  "발달",
  "발레",
  "발목",
  "발바닥",
  "발생",
  "발음",
  "발자국",
  "발전",
  "발톱",
  "발표",
  "밤하늘",
  "밥그릇",
  "밥맛",
  "밥상",
  "밥솥",
  "방금",
  "방면",
  "방문",
  "방바닥",
  "방법",
  "방송",
  "방식",
  "방안",
  "방울",
  "방지",
  "방학",
  "방해",
  "방향",
  "배경",
  "배꼽",
  "배달",
  "배드민턴",
  "백두산",
  "백색",
  "백성",
  "백인",
  "백제",
  "백화점",
  "버릇",
  "버섯",
  "버튼",
  "번개",
  "번역",
  "번지",
  "번호",
  "벌금",
  "벌레",
  "벌써",
  "범위",
  "범인",
  "범죄",
  "법률",
  "법원",
  "법적",
  "법칙",
  "베이징",
  "벨트",
  "변경",
  "변동",
  "변명",
  "변신",
  "변호사",
  "변화",
  "별도",
  "별명",
  "별일",
  "병실",
  "병아리",
  "병원",
  "보관",
  "보너스",
  "보라색",
  "보람",
  "보름",
  "보상",
  "보안",
  "보자기",
  "보장",
  "보전",
  "보존",
  "보통",
  "보편적",
  "보험",
  "복도",
  "복사",
  "복숭아",
  "복습",
  "볶음",
  "본격적",
  "본래",
  "본부",
  "본사",
  "본성",
  "본인",
  "본질",
  "볼펜",
  "봉사",
  "봉지",
  "봉투",
  "부근",
  "부끄러움",
  "부담",
  "부동산",
  "부문",
  "부분",
  "부산",
  "부상",
  "부엌",
  "부인",
  "부작용",
  "부장",
  "부정",
  "부족",
  "부지런히",
  "부친",
  "부탁",
  "부품",
  "부회장",
  "북부",
  "북한",
  "분노",
  "분량",
  "분리",
  "분명",
  "분석",
  "분야",
  "분위기",
  "분필",
  "분홍색",
  "불고기",
  "불과",
  "불교",
  "불꽃",
  "불만",
  "불법",
  "불빛",
  "불안",
  "불이익",
  "불행",
  "브랜드",
  "비극",
  "비난",
  "비닐",
  "비둘기",
  "비디오",
  "비로소",
  "비만",
  "비명",
  "비밀",
  "비바람",
  "비빔밥",
  "비상",
  "비용",
  "비율",
  "비중",
  "비타민",
  "비판",
  "빌딩",
  "빗물",
  "빗방울",
  "빗줄기",
  "빛깔",
  "빨간색",
  "빨래",
  "빨리",
  "사건",
  "사계절",
  "사나이",
  "사냥",
  "사람",
  "사랑",
  "사립",
  "사모님",
  "사물",
  "사방",
  "사상",
  "사생활",
  "사설",
  "사슴",
  "사실",
  "사업",
  "사용",
  "사월",
  "사장",
  "사전",
  "사진",
  "사촌",
  "사춘기",
  "사탕",
  "사투리",
  "사흘",
  "산길",
  "산부인과",
  "산업",
  "산책",
  "살림",
  "살인",
  "살짝",
  "삼계탕",
  "삼국",
  "삼십",
  "삼월",
  "삼촌",
  "상관",
  "상금",
  "상대",
  "상류",
  "상반기",
  "상상",
  "상식",
  "상업",
  "상인",
  "상자",
  "상점",
  "상처",
  "상추",
  "상태",
  "상표",
  "상품",
  "상황",
  "새벽",
  "색깔",
  "색연필",
  "생각",
  "생명",
  "생물",
  "생방송",
  "생산",
  "생선",
  "생신",
  "생일",
  "생활",
  "서랍",
  "서른",
  "서명",
  "서민",
  "서비스",
  "서양",
  "서울",
  "서적",
  "서점",
  "서쪽",
  "서클",
  "석사",
  "석유",
  "선거",
  "선물",
  "선배",
  "선생",
  "선수",
  "선원",
  "선장",
  "선전",
  "선택",
  "선풍기",
  "설거지",
  "설날",
  "설렁탕",
  "설명",
  "설문",
  "설사",
  "설악산",
  "설치",
  "설탕",
  "섭씨",
  "성공",
  "성당",
  "성명",
  "성별",
  "성인",
  "성장",
  "성적",
  "성질",
  "성함",
  "세금",
  "세미나",
  "세상",
  "세월",
  "세종대왕",
  "세탁",
  "센터",
  "센티미터",
  "셋째",
  "소규모",
  "소극적",
  "소금",
  "소나기",
  "소년",
  "소득",
  "소망",
  "소문",
  "소설",
  "소속",
  "소아과",
  "소용",
  "소원",
  "소음",
  "소중히",
  "소지품",
  "소질",
  "소풍",
  "소형",
  "속담",
  "속도",
  "속옷",
  "손가락",
  "손길",
  "손녀",
  "손님",
  "손등",
  "손목",
  "손뼉",
  "손실",
  "손질",
  "손톱",
  "손해",
  "솔직히",
  "솜씨",
  "송아지",
  "송이",
  "송편",
  "쇠고기",
  "쇼핑",
  "수건",
  "수년",
  "수단",
  "수돗물",
  "수동적",
  "수면",
  "수명",
  "수박",
  "수상",
  "수석",
  "수술",
  "수시로",
  "수업",
  "수염",
  "수영",
  "수입",
  "수준",
  "수집",
  "수출",
  "수컷",
  "수필",
  "수학",
  "수험생",
  "수화기",
  "숙녀",
  "숙소",
  "숙제",
  "순간",
  "순서",
  "순수",
  "순식간",
  "순위",
  "숟가락",
  "술병",
  "술집",
  "숫자",
  "스님",
  "스물",
  "스스로",
  "스승",
  "스웨터",
  "스위치",
  "스케이트",
  "스튜디오",
  "스트레스",
  "스포츠",
  "슬쩍",
  "슬픔",
  "습관",
  "습기",
  "승객",
  "승리",
  "승부",
  "승용차",
  "승진",
  "시각",
  "시간",
  "시골",
  "시금치",
  "시나리오",
  "시댁",
  "시리즈",
  "시멘트",
  "시민",
  "시부모",
  "시선",
  "시설",
  "시스템",
  "시아버지",
  "시어머니",
  "시월",
  "시인",
  "시일",
  "시작",
  "시장",
  "시절",
  "시점",
  "시중",
  "시즌",
  "시집",
  "시청",
  "시합",
  "시험",
  "식구",
  "식기",
  "식당",
  "식량",
  "식료품",
  "식물",
  "식빵",
  "식사",
  "식생활",
  "식초",
  "식탁",
  "식품",
  "신고",
  "신규",
  "신념",
  "신문",
  "신발",
  "신비",
  "신사",
  "신세",
  "신용",
  "신제품",
  "신청",
  "신체",
  "신화",
  "실감",
  "실내",
  "실력",
  "실례",
  "실망",
  "실수",
  "실습",
  "실시",
  "실장",
  "실정",
  "실질적",
  "실천",
  "실체",
  "실컷",
  "실태",
  "실패",
  "실험",
  "실현",
  "심리",
  "심부름",
  "심사",
  "심장",
  "심정",
  "심판",
  "쌍둥이",
  "씨름",
  "씨앗",
  "아가씨",
  "아나운서",
  "아드님",
  "아들",
  "아쉬움",
  "아스팔트",
  "아시아",
  "아울러",
  "아저씨",
  "아줌마",
  "아직",
  "아침",
  "아파트",
  "아프리카",
  "아픔",
  "아홉",
  "아흔",
  "악기",
  "악몽",
  "악수",
  "안개",
  "안경",
  "안과",
  "안내",
  "안녕",
  "안동",
  "안방",
  "안부",
  "안주",
  "알루미늄",
  "알코올",
  "암시",
  "암컷",
  "압력",
  "앞날",
  "앞문",
  "애인",
  "애정",
  "액수",
  "앨범",
  "야간",
  "야단",
  "야옹",
  "약간",
  "약국",
  "약속",
  "약수",
  "약점",
  "약품",
  "약혼녀",
  "양념",
  "양력",
  "양말",
  "양배추",
  "양주",
  "양파",
  "어둠",
  "어려움",
  "어른",
  "어젯밤",
  "어쨌든",
  "어쩌다가",
  "어쩐지",
  "언니",
  "언덕",
  "언론",
  "언어",
  "얼굴",
  "얼른",
  "얼음",
  "얼핏",
  "엄마",
  "업무",
  "업종",
  "업체",
  "엉덩이",
  "엉망",
  "엉터리",
  "엊그제",
  "에너지",
  "에어컨",
  "엔진",
  "여건",
  "여고생",
  "여관",
  "여군",
  "여권",
  "여대생",
  "여덟",
  "여동생",
  "여든",
  "여론",
  "여름",
  "여섯",
  "여성",
  "여왕",
  "여인",
  "여전히",
  "여직원",
  "여학생",
  "여행",
  "역사",
  "역시",
  "역할",
  "연결",
  "연구",
  "연극",
  "연기",
  "연락",
  "연설",
  "연세",
  "연속",
  "연습",
  "연애",
  "연예인",
  "연인",
  "연장",
  "연주",
  "연출",
  "연필",
  "연합",
  "연휴",
  "열기",
  "열매",
  "열쇠",
  "열심히",
  "열정",
  "열차",
  "열흘",
  "염려",
  "엽서",
  "영국",
  "영남",
  "영상",
  "영양",
  "영역",
  "영웅",
  "영원히",
  "영하",
  "영향",
  "영혼",
  "영화",
  "옆구리",
  "옆방",
  "옆집",
  "예감",
  "예금",
  "예방",
  "예산",
  "예상",
  "예선",
  "예술",
  "예습",
  "예식장",
  "예약",
  "예전",
  "예절",
  "예정",
  "예컨대",
  "옛날",
  "오늘",
  "오락",
  "오랫동안",
  "오렌지",
  "오로지",
  "오른발",
  "오븐",
  "오십",
  "오염",
  "오월",
  "오전",
  "오직",
  "오징어",
  "오페라",
  "오피스텔",
  "오히려",
  "옥상",
  "옥수수",
  "온갖",
  "온라인",
  "온몸",
  "온종일",
  "온통",
  "올가을",
  "올림픽",
  "올해",
  "옷차림",
  "와이셔츠",
  "와인",
  "완성",
  "완전",
  "왕비",
  "왕자",
  "왜냐하면",
  "왠지",
  "외갓집",
  "외국",
  "외로움",
  "외삼촌",
  "외출",
  "외침",
  "외할머니",
  "왼발",
  "왼손",
  "왼쪽",
  "요금",
  "요일",
  "요즘",
  "요청",
  "용기",
  "용서",
  "용어",
  "우산",
  "우선",
  "우승",
  "우연히",
  "우정",
  "우체국",
  "우편",
  "운동",
  "운명",
  "운반",
  "운전",
  "운행",
  "울산",
  "울음",
  "움직임",
  "웃어른",
  "웃음",
  "워낙",
  "원고",
  "원래",
  "원서",
  "원숭이",
  "원인",
  "원장",
  "원피스",
  "월급",
  "월드컵",
  "월세",
  "월요일",
  "웨이터",
  "위반",
  "위법",
  "위성",
  "위원",
  "위험",
  "위협",
  "윗사람",
  "유난히",
  "유럽",
  "유명",
  "유물",
  "유산",
  "유적",
  "유치원",
  "유학",
  "유행",
  "유형",
  "육군",
  "육상",
  "육십",
  "육체",
  "은행",
  "음력",
  "음료",
  "음반",
  "음성",
  "음식",
  "음악",
  "음주",
  "의견",
  "의논",
  "의문",
  "의복",
  "의식",
  "의심",
  "의외로",
  "의욕",
  "의원",
  "의학",
  "이것",
  "이곳",
  "이념",
  "이놈",
  "이달",
  "이대로",
  "이동",
  "이렇게",
  "이력서",
  "이론적",
  "이름",
  "이민",
  "이발소",
  "이별",
  "이불",
  "이빨",
  "이상",
  "이성",
  "이슬",
  "이야기",
  "이용",
  "이웃",
  "이월",
  "이윽고",
  "이익",
  "이전",
  "이중",
  "이튿날",
  "이틀",
  "이혼",
  "인간",
  "인격",
  "인공",
  "인구",
  "인근",
  "인기",
  "인도",
  "인류",
  "인물",
  "인생",
  "인쇄",
  "인연",
  "인원",
  "인재",
  "인종",
  "인천",
  "인체",
  "인터넷",
  "인하",
  "인형",
  "일곱",
  "일기",
  "일단",
  "일대",
  "일등",
  "일반",
  "일본",
  "일부",
  "일상",
  "일생",
  "일손",
  "일요일",
  "일월",
  "일정",
  "일종",
  "일주일",
  "일찍",
  "일체",
  "일치",
  "일행",
  "일회용",
  "임금",
  "임무",
  "입대",
  "입력",
  "입맛",
  "입사",
  "입술",
  "입시",
  "입원",
  "입장",
  "입학",
  "자가용",
  "자격",
  "자극",
  "자동",
  "자랑",
  "자부심",
  "자식",
  "자신",
  "자연",
  "자원",
  "자율",
  "자전거",
  "자정",
  "자존심",
  "자판",
  "작가",
  "작년",
  "작성",
  "작업",
  "작용",
  "작은딸",
  "작품",
  "잔디",
  "잔뜩",
  "잔치",
  "잘못",
  "잠깐",
  "잠수함",
  "잠시",
  "잠옷",
  "잠자리",
  "잡지",
  "장관",
  "장군",
  "장기간",
  "장래",
  "장례",
  "장르",
  "장마",
  "장면",
  "장모",
  "장미",
  "장비",
  "장사",
  "장소",
  "장식",
  "장애인",
  "장인",
  "장점",
  "장차",
  "장학금",
  "재능",
  "재빨리",
  "재산",
  "재생",
  "재작년",
  "재정",
  "재채기",
  "재판",
  "재학",
  "재활용",
  "저것",
  "저고리",
  "저곳",
  "저녁",
  "저런",
  "저렇게",
  "저번",
  "저울",
  "저절로",
  "저축",
  "적극",
  "적당히",
  "적성",
  "적용",
  "적응",
  "전개",
  "전공",
  "전기",
  "전달",
  "전라도",
  "전망",
  "전문",
  "전반",
  "전부",
  "전세",
  "전시",
  "전용",
  "전자",
  "전쟁",
  "전주",
  "전철",
  "전체",
  "전통",
  "전혀",
  "전후",
  "절대",
  "절망",
  "절반",
  "절약",
  "절차",
  "점검",
  "점수",
  "점심",
  "점원",
  "점점",
  "점차",
  "접근",
  "접시",
  "접촉",
  "젓가락",
  "정거장",
  "정도",
  "정류장",
  "정리",
  "정말",
  "정면",
  "정문",
  "정반대",
  "정보",
  "정부",
  "정비",
  "정상",
  "정성",
  "정오",
  "정원",
  "정장",
  "정지",
  "정치",
  "정확히",
  "제공",
  "제과점",
  "제대로",
  "제목",
  "제발",
  "제법",
  "제삿날",
  "제안",
  "제일",
  "제작",
  "제주도",
  "제출",
  "제품",
  "제한",
  "조각",
  "조건",
  "조금",
  "조깅",
  "조명",
  "조미료",
  "조상",
  "조선",
  "조용히",
  "조절",
  "조정",
  "조직",
  "존댓말",
  "존재",
  "졸업",
  "졸음",
  "종교",
  "종로",
  "종류",
  "종소리",
  "종업원",
  "종종",
  "종합",
  "좌석",
  "죄인",
  "주관적",
  "주름",
  "주말",
  "주머니",
  "주먹",
  "주문",
  "주민",
  "주방",
  "주변",
  "주식",
  "주인",
  "주일",
  "주장",
  "주전자",
  "주택",
  "준비",
  "줄거리",
  "줄기",
  "줄무늬",
  "중간",
  "중계방송",
  "중국",
  "중년",
  "중단",
  "중독",
  "중반",
  "중부",
  "중세",
  "중소기업",
  "중순",
  "중앙",
  "중요",
  "중학교",
  "즉석",
  "즉시",
  "즐거움",
  "증가",
  "증거",
  "증권",
  "증상",
  "증세",
  "지각",
  "지갑",
  "지경",
  "지극히",
  "지금",
  "지급",
  "지능",
  "지름길",
  "지리산",
  "지방",
  "지붕",
  "지식",
  "지역",
  "지우개",
  "지원",
  "지적",
  "지점",
  "지진",
  "지출",
  "직선",
  "직업",
  "직원",
  "직장",
  "진급",
  "진동",
  "진로",
  "진료",
  "진리",
  "진짜",
  "진찰",
  "진출",
  "진통",
  "진행",
  "질문",
  "질병",
  "질서",
  "짐작",
  "집단",
  "집안",
  "집중",
  "짜증",
  "찌꺼기",
  "차남",
  "차라리",
  "차량",
  "차림",
  "차별",
  "차선",
  "차츰",
  "착각",
  "찬물",
  "찬성",
  "참가",
  "참기름",
  "참새",
  "참석",
  "참여",
  "참외",
  "참조",
  "찻잔",
  "창가",
  "창고",
  "창구",
  "창문",
  "창밖",
  "창작",
  "창조",
  "채널",
  "채점",
  "책가방",
  "책방",
  "책상",
  "책임",
  "챔피언",
  "처벌",
  "처음",
  "천국",
  "천둥",
  "천장",
  "천재",
  "천천히",
  "철도",
  "철저히",
  "철학",
  "첫날",
  "첫째",
  "청년",
  "청바지",
  "청소",
  "청춘",
  "체계",
  "체력",
  "체온",
  "체육",
  "체중",
  "체험",
  "초등학생",
  "초반",
  "초밥",
  "초상화",
  "초순",
  "초여름",
  "초원",
  "초저녁",
  "초점",
  "초청",
  "초콜릿",
  "촛불",
  "총각",
  "총리",
  "총장",
  "촬영",
  "최근",
  "최상",
  "최선",
  "최신",
  "최악",
  "최종",
  "추석",
  "추억",
  "추진",
  "추천",
  "추측",
  "축구",
  "축소",
  "축제",
  "축하",
  "출근",
  "출발",
  "출산",
  "출신",
  "출연",
  "출입",
  "출장",
  "출판",
  "충격",
  "충고",
  "충돌",
  "충분히",
  "충청도",
  "취업",
  "취직",
  "취향",
  "치약",
  "친구",
  "친척",
  "칠십",
  "칠월",
  "칠판",
  "침대",
  "침묵",
  "침실",
  "칫솔",
  "칭찬",
  "카메라",
  "카운터",
  "칼국수",
  "캐릭터",
  "캠퍼스",
  "캠페인",
  "커튼",
  "컨디션",
  "컬러",
  "컴퓨터",
  "코끼리",
  "코미디",
  "콘서트",
  "콜라",
  "콤플렉스",
  "콩나물",
  "쾌감",
  "쿠데타",
  "크림",
  "큰길",
  "큰딸",
  "큰소리",
  "큰아들",
  "큰어머니",
  "큰일",
  "큰절",
  "클래식",
  "클럽",
  "킬로",
  "타입",
  "타자기",
  "탁구",
  "탁자",
  "탄생",
  "태권도",
  "태양",
  "태풍",
  "택시",
  "탤런트",
  "터널",
  "터미널",
  "테니스",
  "테스트",
  "테이블",
  "텔레비전",
  "토론",
  "토마토",
  "토요일",
  "통계",
  "통과",
  "통로",
  "통신",
  "통역",
  "통일",
  "통장",
  "통제",
  "통증",
  "통합",
  "통화",
  "퇴근",
  "퇴원",
  "퇴직금",
  "튀김",
  "트럭",
  "특급",
  "특별",
  "특성",
  "특수",
  "특징",
  "특히",
  "튼튼히",
  "티셔츠",
  "파란색",
  "파일",
  "파출소",
  "판결",
  "판단",
  "판매",
  "판사",
  "팔십",
  "팔월",
  "팝송",
  "패션",
  "팩스",
  "팩시밀리",
  "팬티",
  "퍼센트",
  "페인트",
  "편견",
  "편의",
  "편지",
  "편히",
  "평가",
  "평균",
  "평생",
  "평소",
  "평양",
  "평일",
  "평화",
  "포스터",
  "포인트",
  "포장",
  "포함",
  "표면",
  "표정",
  "표준",
  "표현",
  "품목",
  "품질",
  "풍경",
  "풍속",
  "풍습",
  "프랑스",
  "프린터",
  "플라스틱",
  "피곤",
  "피망",
  "피아노",
  "필름",
  "필수",
  "필요",
  "필자",
  "필통",
  "핑계",
  "하느님",
  "하늘",
  "하드웨어",
  "하룻밤",
  "하반기",
  "하숙집",
  "하순",
  "하여튼",
  "하지만",
  "하천",
  "하품",
  "하필",
  "학과",
  "학교",
  "학급",
  "학기",
  "학년",
  "학력",
  "학번",
  "학부모",
  "학비",
  "학생",
  "학술",
  "학습",
  "학용품",
  "학원",
  "학위",
  "학자",
  "학점",
  "한계",
  "한글",
  "한꺼번에",
  "한낮",
  "한눈",
  "한동안",
  "한때",
  "한라산",
  "한마디",
  "한문",
  "한번",
  "한복",
  "한식",
  "한여름",
  "한쪽",
  "할머니",
  "할아버지",
  "할인",
  "함께",
  "함부로",
  "합격",
  "합리적",
  "항공",
  "항구",
  "항상",
  "항의",
  "해결",
  "해군",
  "해답",
  "해당",
  "해물",
  "해석",
  "해설",
  "해수욕장",
  "해안",
  "핵심",
  "핸드백",
  "햄버거",
  "햇볕",
  "햇살",
  "행동",
  "행복",
  "행사",
  "행운",
  "행위",
  "향기",
  "향상",
  "향수",
  "허락",
  "허용",
  "헬기",
  "현관",
  "현금",
  "현대",
  "현상",
  "현실",
  "현장",
  "현재",
  "현지",
  "혈액",
  "협력",
  "형부",
  "형사",
  "형수",
  "형식",
  "형제",
  "형태",
  "형편",
  "혜택",
  "호기심",
  "호남",
  "호랑이",
  "호박",
  "호텔",
  "호흡",
  "혹시",
  "홀로",
  "홈페이지",
  "홍보",
  "홍수",
  "홍차",
  "화면",
  "화분",
  "화살",
  "화요일",
  "화장",
  "화학",
  "확보",
  "확인",
  "확장",
  "확정",
  "환갑",
  "환경",
  "환영",
  "환율",
  "환자",
  "활기",
  "활동",
  "활발히",
  "활용",
  "활짝",
  "회견",
  "회관",
  "회복",
  "회색",
  "회원",
  "회장",
  "회전",
  "횟수",
  "횡단보도",
  "효율적",
  "후반",
  "후춧가루",
  "훈련",
  "훨씬",
  "휴식",
  "휴일",
  "흉내",
  "흐름",
  "흑백",
  "흑인",
  "흔적",
  "흔히",
  "흥미",
  "흥분",
  "희곡",
  "희망",
  "희생",
  "흰색",
  "힘껏"
]
</script>
        <script>WORDLISTS = typeof WORDLISTS == "undefined" ? {} : WORDLISTS;
WORDLISTS["czech"] = ["abdikace","abeceda","adresa","agrese","akce","aktovka","alej","alkohol",
"amputace","ananas","andulka","anekdota","anketa","antika","anulovat","archa","arogance","asfalt",
"asistent","aspirace","astma","astronom","atlas","atletika","atol","autobus","azyl","babka",
"bachor","bacil","baculka","badatel","bageta","bagr","bahno","bakterie","balada","baletka","balkon",
"balonek","balvan","balza","bambus","bankomat","barbar","baret","barman","baroko","barva","baterka",
"batoh","bavlna","bazalka","bazilika","bazuka","bedna","beran","beseda","bestie","beton","bezinka",
"bezmoc","beztak","bicykl","bidlo","biftek","bikiny","bilance","biograf","biolog","bitva","bizon",
"blahobyt","blatouch","blecha","bledule","blesk","blikat","blizna","blokovat","bloudit","blud",
"bobek","bobr","bodlina","bodnout","bohatost","bojkot","bojovat","bokorys","bolest","borec",
"borovice","bota","boubel","bouchat","bouda","boule","bourat","boxer","bradavka","brambora",
"branka","bratr","brepta","briketa","brko","brloh","bronz","broskev","brunetka","brusinka","brzda",
"brzy","bublina","bubnovat","buchta","buditel","budka","budova","bufet","bujarost","bukvice",
"buldok","bulva","bunda","bunkr","burza","butik","buvol","buzola","bydlet","bylina","bytovka","bzukot","capart","carevna","cedr","cedule","cejch","cejn","cela","celer","celkem","celnice","cenina","cennost","cenovka","centrum","cenzor","cestopis","cetka","chalupa","chapadlo","charita","chata","chechtat","chemie","chichot","chirurg","chlad","chleba","chlubit","chmel","chmura","chobot","chochol","chodba","cholera","chomout","chopit","choroba","chov","chrapot","chrlit","chrt","chrup","chtivost","chudina","chutnat","chvat","chvilka","chvost","chyba","chystat","chytit","cibule","cigareta","cihelna","cihla","cinkot","cirkus","cisterna","citace","citrus","cizinec","cizost","clona","cokoliv","couvat","ctitel","ctnost","cudnost","cuketa","cukr","cupot","cvaknout","cval","cvik","cvrkot","cyklista","daleko","dareba","datel","datum","dcera","debata","dechovka","decibel","deficit","deflace","dekl","dekret","demokrat","deprese","derby","deska","detektiv","dikobraz","diktovat","dioda","diplom","disk","displej","divadlo","divoch","dlaha","dlouho","dluhopis","dnes","dobro","dobytek","docent","dochutit","dodnes","dohled","dohoda","dohra","dojem","dojnice","doklad","dokola","doktor","dokument","dolar","doleva","dolina","doma","dominant","domluvit","domov","donutit","dopad","dopis","doplnit","doposud","doprovod","dopustit","dorazit","dorost","dort","dosah","doslov","dostatek","dosud","dosyta","dotaz","dotek","dotknout","doufat","doutnat","dovozce","dozadu","doznat","dozorce","drahota","drak","dramatik","dravec","draze","drdol","drobnost","drogerie","drozd","drsnost","drtit","drzost","duben","duchovno","dudek","duha","duhovka","dusit","dusno","dutost","dvojice","dvorec","dynamit","ekolog","ekonomie","elektron","elipsa","email","emise","emoce","empatie","epizoda","epocha","epopej","epos","esej","esence","eskorta","eskymo","etiketa","euforie","evoluce","exekuce","exkurze","expedice","exploze","export","extrakt","facka","fajfka","fakulta","fanatik","fantazie","farmacie","favorit","fazole","federace","fejeton","fenka","fialka","figurant","filozof","filtr","finance","finta","fixace","fjord","flanel","flirt","flotila","fond","fosfor","fotbal","fotka","foton","frakce","freska","fronta","fukar","funkce","fyzika","galeje","garant","genetika","geolog","gilotina","glazura","glejt","golem","golfista","gotika","graf","gramofon","granule","grep","gril","grog","groteska","guma","hadice","hadr","hala","halenka","hanba","hanopis","harfa","harpuna","havran","hebkost","hejkal","hejno","hejtman","hektar","helma","hematom","herec","herna","heslo","hezky","historik","hladovka","hlasivky","hlava","hledat","hlen","hlodavec","hloh","hloupost","hltat","hlubina","hluchota","hmat","hmota","hmyz","hnis","hnojivo","hnout","hoblina","hoboj","hoch","hodiny","hodlat","hodnota","hodovat","hojnost","hokej","holinka","holka","holub","homole","honitba","honorace","horal","horda","horizont","horko","horlivec","hormon","hornina","horoskop","horstvo","hospoda","hostina","hotovost","houba","houf","houpat","houska","hovor","hradba","hranice","hravost","hrazda","hrbolek","hrdina","hrdlo","hrdost","hrnek","hrobka","hromada","hrot","hrouda","hrozen","hrstka","hrubost","hryzat","hubenost","hubnout","hudba","hukot","humr","husita","hustota","hvozd","hybnost","hydrant","hygiena","hymna","hysterik","idylka","ihned","ikona","iluze","imunita","infekce","inflace","inkaso","inovace","inspekce","internet","invalida","investor","inzerce","ironie","jablko","jachta","jahoda","jakmile","jakost","jalovec","jantar","jarmark","jaro","jasan","jasno","jatka","javor","jazyk","jedinec","jedle","jednatel","jehlan","jekot","jelen","jelito","jemnost","jenom","jepice","jeseter","jevit","jezdec","jezero","jinak","jindy","jinoch","jiskra","jistota","jitrnice","jizva","jmenovat","jogurt","jurta","kabaret","kabel","kabinet","kachna","kadet","kadidlo","kahan","kajak","kajuta","kakao","kaktus","kalamita","kalhoty","kalibr","kalnost","kamera","kamkoliv","kamna","kanibal","kanoe","kantor","kapalina","kapela","kapitola","kapka","kaple","kapota","kapr","kapusta","kapybara","karamel","karotka","karton","kasa","katalog","katedra","kauce","kauza","kavalec","kazajka","kazeta","kazivost","kdekoliv","kdesi","kedluben","kemp","keramika","kino","klacek","kladivo","klam","klapot","klasika","klaun","klec","klenba","klepat","klesnout","klid","klima","klisna","klobouk","klokan","klopa","kloub","klubovna","klusat","kluzkost","kmen","kmitat","kmotr","kniha","knot","koalice","koberec","kobka","kobliha","kobyla","kocour","kohout","kojenec","kokos","koktejl","kolaps","koleda","kolize","kolo","komando","kometa","komik","komnata","komora","kompas","komunita","konat","koncept","kondice","konec","konfese","kongres","konina","konkurs","kontakt","konzerva","kopanec","kopie","kopnout","koprovka","korbel","korektor","kormidlo","koroptev","korpus","koruna","koryto","korzet","kosatec","kostka","kotel","kotleta","kotoul","koukat","koupelna","kousek","kouzlo","kovboj","koza","kozoroh","krabice","krach","krajina","kralovat","krasopis","kravata","kredit","krejcar","kresba","kreveta","kriket","kritik","krize","krkavec","krmelec","krmivo","krocan","krok","kronika","kropit","kroupa","krovka","krtek","kruhadlo","krupice","krutost","krvinka","krychle","krypta","krystal","kryt","kudlanka","kufr","kujnost","kukla","kulajda","kulich","kulka","kulomet","kultura","kuna","kupodivu","kurt","kurzor","kutil","kvalita","kvasinka","kvestor","kynolog","kyselina","kytara","kytice","kytka","kytovec","kyvadlo","labrador","lachtan","ladnost","laik","lakomec","lamela","lampa","lanovka","lasice","laso","lastura","latinka","lavina","lebka","leckdy","leden","lednice","ledovka","ledvina","legenda","legie","legrace","lehce","lehkost","lehnout","lektvar","lenochod","lentilka","lepenka","lepidlo","letadlo","letec","letmo","letokruh","levhart","levitace","levobok","libra","lichotka","lidojed","lidskost","lihovina","lijavec","lilek","limetka","linie","linka","linoleum","listopad","litina","litovat","lobista","lodivod","logika","logoped","lokalita","loket","lomcovat","lopata","lopuch","lord","losos","lotr","loudal","louh","louka","louskat","lovec","lstivost","lucerna","lucifer","lump","lusk","lustrace","lvice","lyra","lyrika","lysina","madam","madlo","magistr","mahagon","majetek","majitel","majorita","makak","makovice","makrela","malba","malina","malovat","malvice","maminka","mandle","manko","marnost","masakr","maskot","masopust","matice","matrika","maturita","mazanec","mazivo","mazlit","mazurka","mdloba","mechanik","meditace","medovina","melasa","meloun","mentolka","metla","metoda","metr","mezera","migrace","mihnout","mihule","mikina","mikrofon","milenec","milimetr","milost","mimika","mincovna","minibar","minomet","minulost","miska","mistr","mixovat","mladost","mlha","mlhovina","mlok","mlsat","mluvit","mnich","mnohem","mobil","mocnost","modelka","modlitba","mohyla","mokro","molekula","momentka","monarcha","monokl","monstrum","montovat","monzun","mosaz","moskyt","most","motivace","motorka","motyka","moucha","moudrost","mozaika","mozek","mozol","mramor","mravenec","mrkev","mrtvola","mrzet","mrzutost","mstitel","mudrc","muflon","mulat","mumie","munice","muset","mutace","muzeum","muzikant","myslivec","mzda","nabourat","nachytat","nadace","nadbytek","nadhoz","nadobro","nadpis","nahlas","nahnat","nahodile","nahradit","naivita","najednou","najisto","najmout","naklonit","nakonec","nakrmit","nalevo","namazat","namluvit","nanometr","naoko","naopak","naostro","napadat","napevno","naplnit","napnout","naposled","naprosto","narodit","naruby","narychlo","nasadit","nasekat","naslepo","nastat","natolik","navenek","navrch","navzdory","nazvat","nebe","nechat","necky","nedaleko","nedbat","neduh","negace","nehet","nehoda","nejen","nejprve","neklid","nelibost","nemilost","nemoc","neochota","neonka","nepokoj","nerost","nerv","nesmysl","nesoulad","netvor","neuron","nevina","nezvykle","nicota","nijak","nikam","nikdy","nikl","nikterak","nitro","nocleh","nohavice","nominace","nora","norek","nositel","nosnost","nouze","noviny","novota","nozdra","nuda","nudle","nuget","nutit","nutnost","nutrie","nymfa","obal","obarvit","obava","obdiv","obec","obehnat","obejmout","obezita","obhajoba","obilnice","objasnit","objekt","obklopit","oblast","oblek","obliba","obloha","obluda","obnos","obohatit","obojek","obout","obrazec","obrna","obruba","obrys","obsah","obsluha","obstarat","obuv","obvaz","obvinit","obvod","obvykle","obyvatel","obzor","ocas","ocel","ocenit","ochladit","ochota","ochrana","ocitnout","odboj","odbyt","odchod","odcizit","odebrat","odeslat","odevzdat","odezva","odhadce","odhodit","odjet","odjinud","odkaz","odkoupit","odliv","odluka","odmlka","odolnost","odpad","odpis","odplout","odpor","odpustit","odpykat","odrazka","odsoudit","odstup","odsun","odtok","odtud","odvaha","odveta","odvolat","odvracet","odznak","ofina","ofsajd","ohlas","ohnisko","ohrada","ohrozit","ohryzek","okap","okenice","oklika","okno","okouzlit","okovy","okrasa","okres","okrsek","okruh","okupant","okurka","okusit","olejnina","olizovat","omak","omeleta","omezit","omladina","omlouvat","omluva","omyl","onehdy","opakovat","opasek","operace","opice","opilost","opisovat","opora","opozice","opravdu","oproti","orbital","orchestr","orgie","orlice","orloj","ortel","osada","oschnout","osika","osivo","oslava","oslepit","oslnit","oslovit","osnova","osoba","osolit","ospalec","osten","ostraha","ostuda","ostych","osvojit","oteplit","otisk","otop","otrhat","otrlost","otrok","otruby","otvor","ovanout","ovar","oves","ovlivnit","ovoce","oxid","ozdoba","pachatel","pacient","padouch","pahorek","pakt","palanda","palec","palivo","paluba","pamflet","pamlsek","panenka","panika","panna","panovat","panstvo","pantofle","paprika","parketa","parodie","parta","paruka","paryba","paseka","pasivita","pastelka","patent","patrona","pavouk","pazneht","pazourek","pecka","pedagog","pejsek","peklo","peloton","penalta","pendrek","penze","periskop","pero","pestrost","petarda","petice","petrolej","pevnina","pexeso","pianista","piha","pijavice","pikle","piknik","pilina","pilnost","pilulka","pinzeta","pipeta","pisatel","pistole","pitevna","pivnice","pivovar","placenta","plakat","plamen","planeta","plastika","platit","plavidlo","plaz","plech","plemeno","plenta","ples","pletivo","plevel","plivat","plnit","plno","plocha","plodina","plomba","plout","pluk","plyn","pobavit","pobyt","pochod","pocit","poctivec","podat","podcenit","podepsat","podhled","podivit","podklad","podmanit","podnik","podoba","podpora","podraz","podstata","podvod","podzim","poezie","pohanka","pohnutka","pohovor","pohroma","pohyb","pointa","pojistka","pojmout","pokazit","pokles","pokoj","pokrok","pokuta","pokyn","poledne","polibek","polknout","poloha","polynom","pomalu","pominout","pomlka","pomoc","pomsta","pomyslet","ponechat","ponorka","ponurost","popadat","popel","popisek","poplach","poprosit","popsat","popud","poradce","porce","porod","porucha","poryv","posadit","posed","posila","poskok","poslanec","posoudit","pospolu","postava","posudek","posyp","potah","potkan","potlesk","potomek","potrava","potupa","potvora","poukaz","pouto","pouzdro","povaha","povidla","povlak","povoz","povrch","povstat","povyk","povzdech","pozdrav","pozemek","poznatek","pozor","pozvat","pracovat","prahory","praktika","prales","praotec","praporek","prase","pravda","princip","prkno","probudit","procento","prodej","profese","prohra","projekt","prolomit","promile","pronikat","propad","prorok","prosba","proton","proutek","provaz","prskavka","prsten","prudkost","prut","prvek","prvohory","psanec","psovod","pstruh","ptactvo","puberta","puch","pudl","pukavec","puklina","pukrle","pult","pumpa","punc","pupen","pusa","pusinka","pustina","putovat","putyka","pyramida","pysk","pytel","racek","rachot","radiace","radnice","radon","raft","ragby","raketa","rakovina","rameno","rampouch","rande","rarach","rarita","rasovna","rastr","ratolest","razance","razidlo","reagovat","reakce","recept","redaktor","referent","reflex","rejnok","reklama","rekord","rekrut","rektor","reputace","revize","revma","revolver","rezerva","riskovat","riziko","robotika","rodokmen","rohovka","rokle","rokoko","romaneto","ropovod","ropucha","rorejs","rosol","rostlina","rotmistr","rotoped","rotunda","roubenka","roucho","roup","roura","rovina","rovnice","rozbor","rozchod","rozdat","rozeznat","rozhodce","rozinka","rozjezd","rozkaz","rozloha","rozmar","rozpad","rozruch","rozsah","roztok","rozum","rozvod","rubrika","ruchadlo","rukavice","rukopis","ryba","rybolov","rychlost","rydlo","rypadlo","rytina","ryzost","sadista","sahat","sako","samec","samizdat","samota","sanitka","sardinka","sasanka","satelit","sazba","sazenice","sbor","schovat","sebranka","secese","sedadlo","sediment","sedlo","sehnat","sejmout","sekera","sekta","sekunda","sekvoje","semeno","seno","servis","sesadit","seshora","seskok","seslat","sestra","sesuv","sesypat","setba","setina","setkat","setnout","setrvat","sever","seznam","shoda","shrnout","sifon","silnice","sirka","sirotek","sirup","situace","skafandr","skalisko","skanzen","skaut","skeptik","skica","skladba","sklenice","sklo","skluz","skoba","skokan","skoro","skripta","skrz","skupina","skvost","skvrna","slabika","sladidlo","slanina","slast","slavnost","sledovat","slepec","sleva","slezina","slib","slina","sliznice","slon","sloupek","slovo","sluch","sluha","slunce","slupka","slza","smaragd","smetana","smilstvo","smlouva","smog","smrad","smrk","smrtka","smutek","smysl","snad","snaha","snob","sobota","socha","sodovka","sokol","sopka","sotva","souboj","soucit","soudce","souhlas","soulad","soumrak","souprava","soused","soutok","souviset","spalovna","spasitel","spis","splav","spodek","spojenec","spolu","sponzor","spornost","spousta","sprcha","spustit","sranda","sraz","srdce","srna","srnec","srovnat","srpen","srst","srub","stanice","starosta","statika","stavba","stehno","stezka","stodola","stolek","stopa","storno","stoupat","strach","stres","strhnout","strom","struna","studna","stupnice","stvol","styk","subjekt","subtropy","suchar","sudost","sukno","sundat","sunout","surikata","surovina","svah","svalstvo","svetr","svatba","svazek","svisle","svitek","svoboda","svodidlo","svorka","svrab","sykavka","sykot","synek","synovec","sypat","sypkost","syrovost","sysel","sytost","tabletka","tabule","tahoun","tajemno","tajfun","tajga","tajit","tajnost","taktika","tamhle","tampon","tancovat","tanec","tanker","tapeta","tavenina","tazatel","technika","tehdy","tekutina","telefon","temnota","tendence","tenista","tenor","teplota","tepna","teprve","terapie","termoska","textil","ticho","tiskopis","titulek","tkadlec","tkanina","tlapka","tleskat","tlukot","tlupa","tmel","toaleta","topinka","topol","torzo","touha","toulec","tradice","traktor","tramp","trasa","traverza","trefit","trest","trezor","trhavina","trhlina","trochu","trojice","troska","trouba","trpce","trpitel","trpkost","trubec","truchlit","truhlice","trus","trvat","tudy","tuhnout","tuhost","tundra","turista","turnaj","tuzemsko","tvaroh","tvorba","tvrdost","tvrz","tygr","tykev","ubohost","uboze","ubrat","ubrousek","ubrus","ubytovna","ucho","uctivost","udivit","uhradit","ujednat","ujistit","ujmout","ukazatel","uklidnit","uklonit","ukotvit","ukrojit","ulice","ulita","ulovit","umyvadlo","unavit","uniforma","uniknout","upadnout","uplatnit","uplynout","upoutat","upravit","uran","urazit","usednout","usilovat","usmrtit","usnadnit","usnout","usoudit","ustlat","ustrnout","utahovat","utkat","utlumit","utonout","utopenec","utrousit","uvalit","uvolnit","uvozovka","uzdravit","uzel","uzenina","uzlina","uznat","vagon","valcha","valoun","vana","vandal","vanilka","varan","varhany","varovat","vcelku","vchod","vdova","vedro","vegetace","vejce","velbloud","veletrh","velitel","velmoc","velryba","venkov","veranda","verze","veselka","veskrze","vesnice","vespodu","vesta","veterina","veverka","vibrace","vichr","videohra","vidina","vidle","vila","vinice","viset","vitalita","vize","vizitka","vjezd","vklad","vkus","vlajka","vlak","vlasec","vlevo","vlhkost","vliv","vlnovka","vloupat","vnucovat","vnuk","voda","vodivost","vodoznak","vodstvo","vojensky","vojna","vojsko","volant","volba","volit","volno","voskovka","vozidlo","vozovna","vpravo","vrabec","vracet","vrah","vrata","vrba","vrcholek","vrhat","vrstva","vrtule","vsadit","vstoupit","vstup","vtip","vybavit","vybrat","vychovat","vydat","vydra","vyfotit","vyhledat","vyhnout","vyhodit","vyhradit","vyhubit","vyjasnit","vyjet","vyjmout","vyklopit","vykonat","vylekat","vymazat","vymezit","vymizet","vymyslet","vynechat","vynikat","vynutit","vypadat","vyplatit","vypravit","vypustit","vyrazit","vyrovnat","vyrvat","vyslovit","vysoko","vystavit","vysunout","vysypat","vytasit","vytesat","vytratit","vyvinout","vyvolat","vyvrhel","vyzdobit","vyznat","vzadu","vzbudit","vzchopit","vzdor","vzduch","vzdychat","vzestup","vzhledem","vzkaz","vzlykat","vznik","vzorek","vzpoura","vztah","vztek","xylofon","zabrat","zabydlet","zachovat","zadarmo","zadusit","zafoukat","zahltit","zahodit","zahrada","zahynout","zajatec","zajet","zajistit","zaklepat","zakoupit","zalepit","zamezit","zamotat","zamyslet","zanechat","zanikat","zaplatit","zapojit","zapsat","zarazit","zastavit","zasunout","zatajit","zatemnit","zatknout","zaujmout","zavalit","zavelet","zavinit","zavolat","zavrtat","zazvonit","zbavit","zbrusu","zbudovat","zbytek","zdaleka","zdarma","zdatnost","zdivo","zdobit","zdroj","zdvih","zdymadlo","zelenina","zeman","zemina","zeptat","zezadu","zezdola","zhatit","zhltnout","zhluboka","zhotovit","zhruba","zima","zimnice","zjemnit","zklamat","zkoumat","zkratka","zkumavka","zlato","zlehka","zloba","zlom","zlost","zlozvyk","zmapovat","zmar","zmatek","zmije","zmizet","zmocnit","zmodrat","zmrzlina","zmutovat","znak","znalost","znamenat","znovu","zobrazit","zotavit","zoubek","zoufale","zplodit","zpomalit","zprava","zprostit","zprudka","zprvu","zrada","zranit","zrcadlo","zrnitost","zrno","zrovna","zrychlit","zrzavost","zticha","ztratit","zubovina","zubr","zvednout","zvenku","zvesela","zvon","zvrat","zvukovod","zvyk"]</script>
        <script>WORDLISTS = typeof
WORDLISTS == "undefined" ? {}: WORDLISTS;
WORDLISTS["portuguese"] = [
    "abacate", "abaixo", "abalar", "abater", "abduzir", "abelha", "aberto", "abismo", "abotoar", "abranger", "abreviar",
    "abrigar", "abrupto", "absinto", "absoluto", "absurdo", "abutre", "acabado", "acalmar", "acampar", "acanhar",
    "acaso", "aceitar", "acelerar", "acenar", "acervo", "acessar", "acetona", "achatar", "acidez", "acima", "acionado",
    "acirrar", "aclamar", "aclive", "acolhida", "acomodar", "acoplar", "acordar", "acumular", "acusador", "adaptar",
    "adega", "adentro", "adepto", "adequar", "aderente", "adesivo", "adeus", "adiante", "aditivo", "adjetivo",
    "adjunto", "admirar", "adorar", "adquirir", "adubo", "adverso", "advogado", "aeronave", "afastar", "aferir",
    "afetivo", "afinador", "afivelar", "aflito", "afluente", "afrontar", "agachar", "agarrar", "agasalho", "agenciar",
    "agilizar", "agiota", "agitado", "agora", "agradar", "agreste", "agrupar", "aguardar", "agulha", "ajoelhar",
    "ajudar", "ajustar", "alameda", "alarme", "alastrar", "alavanca", "albergue", "albino", "alcatra", "aldeia",
    "alecrim", "alegria", "alertar", "alface", "alfinete", "algum", "alheio", "aliar", "alicate", "alienar", "alinhar",
    "aliviar", "almofada", "alocar", "alpiste", "alterar", "altitude", "alucinar", "alugar", "aluno", "alusivo", "alvo",
    "amaciar", "amador", "amarelo", "amassar", "ambas", "ambiente", "ameixa", "amenizar", "amido", "amistoso",
    "amizade", "amolador", "amontoar", "amoroso", "amostra", "amparar", "ampliar", "ampola", "anagrama", "analisar",
    "anarquia", "anatomia", "andaime", "anel", "anexo", "angular", "animar", "anjo", "anomalia", "anotado", "ansioso",
    "anterior", "anuidade", "anunciar", "anzol", "apagador", "apalpar", "apanhado", "apego", "apelido", "apertada",
    "apesar", "apetite", "apito", "aplauso", "aplicada", "apoio", "apontar", "aposta", "aprendiz", "aprovar", "aquecer",
    "arame", "aranha", "arara", "arcada", "ardente", "areia", "arejar", "arenito", "aresta", "argiloso", "argola",
    "arma", "arquivo", "arraial", "arrebate", "arriscar", "arroba", "arrumar", "arsenal", "arterial", "artigo",
    "arvoredo", "asfaltar", "asilado", "aspirar", "assador", "assinar", "assoalho", "assunto", "astral", "atacado",
    "atadura", "atalho", "atarefar", "atear", "atender", "aterro", "ateu", "atingir", "atirador", "ativo", "atoleiro",
    "atracar", "atrevido", "atriz", "atual", "atum", "auditor", "aumentar", "aura", "aurora", "autismo", "autoria",
    "autuar", "avaliar", "avante", "avaria", "avental", "avesso", "aviador", "avisar", "avulso", "axila", "azarar",
    "azedo", "azeite", "azulejo", "babar", "babosa", "bacalhau", "bacharel", "bacia", "bagagem", "baiano", "bailar",
    "baioneta", "bairro", "baixista", "bajular", "baleia", "baliza", "balsa", "banal", "bandeira", "banho", "banir",
    "banquete", "barato", "barbado", "baronesa", "barraca", "barulho", "baseado", "bastante", "batata", "batedor",
    "batida", "batom", "batucar", "baunilha", "beber", "beijo", "beirada", "beisebol", "beldade", "beleza", "belga",
    "beliscar", "bendito", "bengala", "benzer", "berimbau", "berlinda", "berro", "besouro", "bexiga", "bezerro", "bico",
    "bicudo", "bienal", "bifocal", "bifurcar", "bigorna", "bilhete", "bimestre", "bimotor", "biologia", "biombo",
    "biosfera", "bipolar", "birrento", "biscoito", "bisneto", "bispo", "bissexto", "bitola", "bizarro", "blindado",
    "bloco", "bloquear", "boato", "bobagem", "bocado", "bocejo", "bochecha", "boicotar", "bolada", "boletim", "bolha",
    "bolo", "bombeiro", "bonde", "boneco", "bonita", "borbulha", "borda", "boreal", "borracha", "bovino", "boxeador",
    "branco", "brasa", "braveza", "breu", "briga", "brilho", "brincar", "broa", "brochura", "bronzear", "broto",
    "bruxo", "bucha", "budismo", "bufar", "bule", "buraco", "busca", "busto", "buzina", "cabana", "cabelo", "cabide",
    "cabo", "cabrito", "cacau", "cacetada", "cachorro", "cacique", "cadastro", "cadeado", "cafezal", "caiaque",
    "caipira", "caixote", "cajado", "caju", "calafrio", "calcular", "caldeira", "calibrar", "calmante", "calota",
    "camada", "cambista", "camisa", "camomila", "campanha", "camuflar", "canavial", "cancelar", "caneta", "canguru",
    "canhoto", "canivete", "canoa", "cansado", "cantar", "canudo", "capacho", "capela", "capinar", "capotar",
    "capricho", "captador", "capuz", "caracol", "carbono", "cardeal", "careca", "carimbar", "carneiro", "carpete",
    "carreira", "cartaz", "carvalho", "casaco", "casca", "casebre", "castelo", "casulo", "catarata", "cativar", "caule",
    "causador", "cautelar", "cavalo", "caverna", "cebola", "cedilha", "cegonha", "celebrar", "celular", "cenoura",
    "censo", "centeio", "cercar", "cerrado", "certeiro", "cerveja", "cetim", "cevada", "chacota", "chaleira", "chamado",
    "chapada", "charme", "chatice", "chave", "chefe", "chegada", "cheiro", "cheque", "chicote", "chifre", "chinelo",
    "chocalho", "chover", "chumbo", "chutar", "chuva", "cicatriz", "ciclone", "cidade", "cidreira", "ciente", "cigana",
    "cimento", "cinto", "cinza", "ciranda", "circuito", "cirurgia", "citar", "clareza", "clero", "clicar", "clone",
    "clube", "coado", "coagir", "cobaia", "cobertor", "cobrar", "cocada", "coelho", "coentro", "coeso", "cogumelo",
    "coibir", "coifa", "coiote", "colar", "coleira", "colher", "colidir", "colmeia", "colono", "coluna", "comando",
    "combinar", "comentar", "comitiva", "comover", "complexo", "comum", "concha", "condor", "conectar", "confuso",
    "congelar", "conhecer", "conjugar", "consumir", "contrato", "convite", "cooperar", "copeiro", "copiador", "copo",
    "coquetel", "coragem", "cordial", "corneta", "coronha", "corporal", "correio", "cortejo", "coruja", "corvo",
    "cosseno", "costela", "cotonete", "couro", "couve", "covil", "cozinha", "cratera", "cravo", "creche", "credor",
    "creme", "crer", "crespo", "criada", "criminal", "crioulo", "crise", "criticar", "crosta", "crua", "cruzeiro",
    "cubano", "cueca", "cuidado", "cujo", "culatra", "culminar", "culpar", "cultura", "cumprir", "cunhado", "cupido",
    "curativo", "curral", "cursar", "curto", "cuspir", "custear", "cutelo", "damasco", "datar", "debater", "debitar",
    "deboche", "debulhar", "decalque", "decimal", "declive", "decote", "decretar", "dedal", "dedicado", "deduzir",
    "defesa", "defumar", "degelo", "degrau", "degustar", "deitado", "deixar", "delator", "delegado", "delinear",
    "delonga", "demanda", "demitir", "demolido", "dentista", "depenado", "depilar", "depois", "depressa", "depurar",
    "deriva", "derramar", "desafio", "desbotar", "descanso", "desenho", "desfiado", "desgaste", "desigual", "deslize",
    "desmamar", "desova", "despesa", "destaque", "desviar", "detalhar", "detentor", "detonar", "detrito", "deusa",
    "dever", "devido", "devotado", "dezena", "diagrama", "dialeto", "didata", "difuso", "digitar", "dilatado",
    "diluente", "diminuir", "dinastia", "dinheiro", "diocese", "direto", "discreta", "disfarce", "disparo", "disquete",
    "dissipar", "distante", "ditador", "diurno", "diverso", "divisor", "divulgar", "dizer", "dobrador", "dolorido",
    "domador", "dominado", "donativo", "donzela", "dormente", "dorsal", "dosagem", "dourado", "doutor", "drenagem",
    "drible", "drogaria", "duelar", "duende", "dueto", "duplo", "duquesa", "durante", "duvidoso", "eclodir", "ecoar",
    "ecologia", "edificar", "edital", "educado", "efeito", "efetivar", "ejetar", "elaborar", "eleger", "eleitor",
    "elenco", "elevador", "eliminar", "elogiar", "embargo", "embolado", "embrulho", "embutido", "emenda", "emergir",
    "emissor", "empatia", "empenho", "empinado", "empolgar", "emprego", "empurrar", "emulador", "encaixe", "encenado",
    "enchente", "encontro", "endeusar", "endossar", "enfaixar", "enfeite", "enfim", "engajado", "engenho", "englobar",
    "engomado", "engraxar", "enguia", "enjoar", "enlatar", "enquanto", "enraizar", "enrolado", "enrugar", "ensaio",
    "enseada", "ensino", "ensopado", "entanto", "enteado", "entidade", "entortar", "entrada", "entulho", "envergar",
    "enviado", "envolver", "enxame", "enxerto", "enxofre", "enxuto", "epiderme", "equipar", "ereto", "erguido",
    "errata", "erva", "ervilha", "esbanjar", "esbelto", "escama", "escola", "escrita", "escuta", "esfinge", "esfolar",
    "esfregar", "esfumado", "esgrima", "esmalte", "espanto", "espelho", "espiga", "esponja", "espreita", "espumar",
    "esquerda", "estaca", "esteira", "esticar", "estofado", "estrela", "estudo", "esvaziar", "etanol", "etiqueta",
    "euforia", "europeu", "evacuar", "evaporar", "evasivo", "eventual", "evidente", "evoluir", "exagero", "exalar",
    "examinar", "exato", "exausto", "excesso", "excitar", "exclamar", "executar", "exemplo", "exibir", "exigente",
    "exonerar", "expandir", "expelir", "expirar", "explanar", "exposto", "expresso", "expulsar", "externo", "extinto",
    "extrato", "fabricar", "fabuloso", "faceta", "facial", "fada", "fadiga", "faixa", "falar", "falta", "familiar",
    "fandango", "fanfarra", "fantoche", "fardado", "farelo", "farinha", "farofa", "farpa", "fartura", "fatia", "fator",
    "favorita", "faxina", "fazenda", "fechado", "feijoada", "feirante", "felino", "feminino", "fenda", "feno", "fera",
    "feriado", "ferrugem", "ferver", "festejar", "fetal", "feudal", "fiapo", "fibrose", "ficar", "ficheiro", "figurado",
    "fileira", "filho", "filme", "filtrar", "firmeza", "fisgada", "fissura", "fita", "fivela", "fixador", "fixo",
    "flacidez", "flamingo", "flanela", "flechada", "flora", "flutuar", "fluxo", "focal", "focinho", "fofocar", "fogo",
    "foguete", "foice", "folgado", "folheto", "forjar", "formiga", "forno", "forte", "fosco", "fossa", "fragata",
    "fralda", "frango", "frasco", "fraterno", "freira", "frente", "fretar", "frieza", "friso", "fritura", "fronha",
    "frustrar", "fruteira", "fugir", "fulano", "fuligem", "fundar", "fungo", "funil", "furador", "furioso", "futebol",
    "gabarito", "gabinete", "gado", "gaiato", "gaiola", "gaivota", "galega", "galho", "galinha", "galocha", "ganhar",
    "garagem", "garfo", "gargalo", "garimpo", "garoupa", "garrafa", "gasoduto", "gasto", "gata", "gatilho", "gaveta",
    "gazela", "gelado", "geleia", "gelo", "gemada", "gemer", "gemido", "generoso", "gengiva", "genial", "genoma",
    "genro", "geologia", "gerador", "germinar", "gesso", "gestor", "ginasta", "gincana", "gingado", "girafa", "girino",
    "glacial", "glicose", "global", "glorioso", "goela", "goiaba", "golfe", "golpear", "gordura", "gorjeta", "gorro",
    "gostoso", "goteira", "governar", "gracejo", "gradual", "grafite", "gralha", "grampo", "granada", "gratuito",
    "graveto", "graxa", "grego", "grelhar", "greve", "grilo", "grisalho", "gritaria", "grosso", "grotesco", "grudado",
    "grunhido", "gruta", "guache", "guarani", "guaxinim", "guerrear", "guiar", "guincho", "guisado", "gula", "guloso",
    "guru", "habitar", "harmonia", "haste", "haver", "hectare", "herdar", "heresia", "hesitar", "hiato", "hibernar",
    "hidratar", "hiena", "hino", "hipismo", "hipnose", "hipoteca", "hoje", "holofote", "homem", "honesto", "honrado",
    "hormonal", "hospedar", "humorado", "iate", "ideia", "idoso", "ignorado", "igreja", "iguana", "ileso", "ilha",
    "iludido", "iluminar", "ilustrar", "imagem", "imediato", "imenso", "imersivo", "iminente", "imitador", "imortal",
    "impacto", "impedir", "implante", "impor", "imprensa", "impune", "imunizar", "inalador", "inapto", "inativo",
    "incenso", "inchar", "incidir", "incluir", "incolor", "indeciso", "indireto", "indutor", "ineficaz", "inerente",
    "infantil", "infestar", "infinito", "inflamar", "informal", "infrator", "ingerir", "inibido", "inicial", "inimigo",
    "injetar", "inocente", "inodoro", "inovador", "inox", "inquieto", "inscrito", "inseto", "insistir", "inspetor",
    "instalar", "insulto", "intacto", "integral", "intimar", "intocado", "intriga", "invasor", "inverno", "invicto",
    "invocar", "iogurte", "iraniano", "ironizar", "irreal", "irritado", "isca", "isento", "isolado", "isqueiro",
    "italiano", "janeiro", "jangada", "janta", "jararaca", "jardim", "jarro", "jasmim", "jato", "javali", "jazida",
    "jejum", "joaninha", "joelhada", "jogador", "joia", "jornal", "jorrar", "jovem", "juba", "judeu", "judoca", "juiz",
    "julgador", "julho", "jurado", "jurista", "juro", "justa", "labareda", "laboral", "lacre", "lactante", "ladrilho",
    "lagarta", "lagoa", "laje", "lamber", "lamentar", "laminar", "lampejo", "lanche", "lapidar", "lapso", "laranja",
    "lareira", "largura", "lasanha", "lastro", "lateral", "latido", "lavanda", "lavoura", "lavrador", "laxante",
    "lazer", "lealdade", "lebre", "legado", "legendar", "legista", "leigo", "leiloar", "leitura", "lembrete", "leme",
    "lenhador", "lentilha", "leoa", "lesma", "leste", "letivo", "letreiro", "levar", "leveza", "levitar", "liberal",
    "libido", "liderar", "ligar", "ligeiro", "limitar", "limoeiro", "limpador", "linda", "linear", "linhagem",
    "liquidez", "listagem", "lisura", "litoral", "livro", "lixa", "lixeira", "locador", "locutor", "lojista", "lombo",
    "lona", "longe", "lontra", "lorde", "lotado", "loteria", "loucura", "lousa", "louvar", "luar", "lucidez", "lucro",
    "luneta", "lustre", "lutador", "luva", "macaco", "macete", "machado", "macio", "madeira", "madrinha", "magnata",
    "magreza", "maior", "mais", "malandro", "malha", "malote", "maluco", "mamilo", "mamoeiro", "mamute", "manada",
    "mancha", "mandato", "manequim", "manhoso", "manivela", "manobrar", "mansa", "manter", "manusear", "mapeado",
    "maquinar", "marcador", "maresia", "marfim", "margem", "marinho", "marmita", "maroto", "marquise", "marreco",
    "martelo", "marujo", "mascote", "masmorra", "massagem", "mastigar", "matagal", "materno", "matinal", "matutar",
    "maxilar", "medalha", "medida", "medusa", "megafone", "meiga", "melancia", "melhor", "membro", "memorial", "menino",
    "menos", "mensagem", "mental", "merecer", "mergulho", "mesada", "mesclar", "mesmo", "mesquita", "mestre", "metade",
    "meteoro", "metragem", "mexer", "mexicano", "micro", "migalha", "migrar", "milagre", "milenar", "milhar", "mimado",
    "minerar", "minhoca", "ministro", "minoria", "miolo", "mirante", "mirtilo", "misturar", "mocidade", "moderno",
    "modular", "moeda", "moer", "moinho", "moita", "moldura", "moleza", "molho", "molinete", "molusco", "montanha",
    "moqueca", "morango", "morcego", "mordomo", "morena", "mosaico", "mosquete", "mostarda", "motel", "motim", "moto",
    "motriz", "muda", "muito", "mulata", "mulher", "multar", "mundial", "munido", "muralha", "murcho", "muscular",
    "museu", "musical", "nacional", "nadador", "naja", "namoro", "narina", "narrado", "nascer", "nativa", "natureza",
    "navalha", "navegar", "navio", "neblina", "nebuloso", "negativa", "negociar", "negrito", "nervoso", "neta",
    "neural", "nevasca", "nevoeiro", "ninar", "ninho", "nitidez", "nivelar", "nobreza", "noite", "noiva", "nomear",
    "nominal", "nordeste", "nortear", "notar", "noticiar", "noturno", "novelo", "novilho", "novo", "nublado", "nudez",
    "numeral", "nupcial", "nutrir", "nuvem", "obcecado", "obedecer", "objetivo", "obrigado", "obscuro", "obstetra",
    "obter", "obturar", "ocidente", "ocioso", "ocorrer", "oculista", "ocupado", "ofegante", "ofensiva", "oferenda",
    "oficina", "ofuscado", "ogiva", "olaria", "oleoso", "olhar", "oliveira", "ombro", "omelete", "omisso", "omitir",
    "ondulado", "oneroso", "ontem", "opcional", "operador", "oponente", "oportuno", "oposto", "orar", "orbitar",
    "ordem", "ordinal", "orfanato", "orgasmo", "orgulho", "oriental", "origem", "oriundo", "orla", "ortodoxo",
    "orvalho", "oscilar", "ossada", "osso", "ostentar", "otimismo", "ousadia", "outono", "outubro", "ouvido", "ovelha",
    "ovular", "oxidar", "oxigenar", "pacato", "paciente", "pacote", "pactuar", "padaria", "padrinho", "pagar", "pagode",
    "painel", "pairar", "paisagem", "palavra", "palestra", "palheta", "palito", "palmada", "palpitar", "pancada",
    "panela", "panfleto", "panqueca", "pantanal", "papagaio", "papelada", "papiro", "parafina", "parcial", "pardal",
    "parede", "partida", "pasmo", "passado", "pastel", "patamar", "patente", "patinar", "patrono", "paulada", "pausar",
    "peculiar", "pedalar", "pedestre", "pediatra", "pedra", "pegada", "peitoral", "peixe", "pele", "pelicano", "penca",
    "pendurar", "peneira", "penhasco", "pensador", "pente", "perceber", "perfeito", "pergunta", "perito", "permitir",
    "perna", "perplexo", "persiana", "pertence", "peruca", "pescado", "pesquisa", "pessoa", "petiscar", "piada",
    "picado", "piedade", "pigmento", "pilastra", "pilhado", "pilotar", "pimenta", "pincel", "pinguim", "pinha",
    "pinote", "pintar", "pioneiro", "pipoca", "piquete", "piranha", "pires", "pirueta", "piscar", "pistola", "pitanga",
    "pivete", "planta", "plaqueta", "platina", "plebeu", "plumagem", "pluvial", "pneu", "poda", "poeira", "poetisa",
    "polegada", "policiar", "poluente", "polvilho", "pomar", "pomba", "ponderar", "pontaria", "populoso", "porta",
    "possuir", "postal", "pote", "poupar", "pouso", "povoar", "praia", "prancha", "prato", "praxe", "prece", "predador",
    "prefeito", "premiar", "prensar", "preparar", "presilha", "pretexto", "prevenir", "prezar", "primata", "princesa",
    "prisma", "privado", "processo", "produto", "profeta", "proibido", "projeto", "prometer", "propagar", "prosa",
    "protetor", "provador", "publicar", "pudim", "pular", "pulmonar", "pulseira", "punhal", "punir", "pupilo", "pureza",
    "puxador", "quadra", "quantia", "quarto", "quase", "quebrar", "queda", "queijo", "quente", "querido", "quimono",
    "quina", "quiosque", "rabanada", "rabisco", "rachar", "racionar", "radial", "raiar", "rainha", "raio", "raiva",
    "rajada", "ralado", "ramal", "ranger", "ranhura", "rapadura", "rapel", "rapidez", "raposa", "raquete", "raridade",
    "rasante", "rascunho", "rasgar", "raspador", "rasteira", "rasurar", "ratazana", "ratoeira", "realeza", "reanimar",
    "reaver", "rebaixar", "rebelde", "rebolar", "recado", "recente", "recheio", "recibo", "recordar", "recrutar",
    "recuar", "rede", "redimir", "redonda", "reduzida", "reenvio", "refinar", "refletir", "refogar", "refresco",
    "refugiar", "regalia", "regime", "regra", "reinado", "reitor", "rejeitar", "relativo", "remador", "remendo",
    "remorso", "renovado", "reparo", "repelir", "repleto", "repolho", "represa", "repudiar", "requerer", "resenha",
    "resfriar", "resgatar", "residir", "resolver", "respeito", "ressaca", "restante", "resumir", "retalho", "reter",
    "retirar", "retomada", "retratar", "revelar", "revisor", "revolta", "riacho", "rica", "rigidez", "rigoroso",
    "rimar", "ringue", "risada", "risco", "risonho", "robalo", "rochedo", "rodada", "rodeio", "rodovia", "roedor",
    "roleta", "romano", "roncar", "rosado", "roseira", "rosto", "rota", "roteiro", "rotina", "rotular", "rouco",
    "roupa", "roxo", "rubro", "rugido", "rugoso", "ruivo", "rumo", "rupestre", "russo", "sabor", "saciar", "sacola",
    "sacudir", "sadio", "safira", "saga", "sagrada", "saibro", "salada", "saleiro", "salgado", "saliva", "salpicar",
    "salsicha", "saltar", "salvador", "sambar", "samurai", "sanar", "sanfona", "sangue", "sanidade", "sapato", "sarda",
    "sargento", "sarjeta", "saturar", "saudade", "saxofone", "sazonal", "secar", "secular", "seda", "sedento",
    "sediado", "sedoso", "sedutor", "segmento", "segredo", "segundo", "seiva", "seleto", "selvagem", "semanal",
    "semente", "senador", "senhor", "sensual", "sentado", "separado", "sereia", "seringa", "serra", "servo", "setembro",
    "setor", "sigilo", "silhueta", "silicone", "simetria", "simpatia", "simular", "sinal", "sincero", "singular",
    "sinopse", "sintonia", "sirene", "siri", "situado", "soberano", "sobra", "socorro", "sogro", "soja", "solda",
    "soletrar", "solteiro", "sombrio", "sonata", "sondar", "sonegar", "sonhador", "sono", "soprano", "soquete",
    "sorrir", "sorteio", "sossego", "sotaque", "soterrar", "sovado", "sozinho", "suavizar", "subida", "submerso",
    "subsolo", "subtrair", "sucata", "sucesso", "suco", "sudeste", "sufixo", "sugador", "sugerir", "sujeito", "sulfato",
    "sumir", "suor", "superior", "suplicar", "suposto", "suprimir", "surdina", "surfista", "surpresa", "surreal",
    "surtir", "suspiro", "sustento", "tabela", "tablete", "tabuada", "tacho", "tagarela", "talher", "talo", "talvez",
    "tamanho", "tamborim", "tampa", "tangente", "tanto", "tapar", "tapioca", "tardio", "tarefa", "tarja", "tarraxa",
    "tatuagem", "taurino", "taxativo", "taxista", "teatral", "tecer", "tecido", "teclado", "tedioso", "teia", "teimar",
    "telefone", "telhado", "tempero", "tenente", "tensor", "tentar", "termal", "terno", "terreno", "tese", "tesoura",
    "testado", "teto", "textura", "texugo", "tiara", "tigela", "tijolo", "timbrar", "timidez", "tingido", "tinteiro",
    "tiragem", "titular", "toalha", "tocha", "tolerar", "tolice", "tomada", "tomilho", "tonel", "tontura", "topete",
    "tora", "torcido", "torneio", "torque", "torrada", "torto", "tostar", "touca", "toupeira", "toxina", "trabalho",
    "tracejar", "tradutor", "trafegar", "trajeto", "trama", "trancar", "trapo", "traseiro", "tratador", "travar",
    "treino", "tremer", "trepidar", "trevo", "triagem", "tribo", "triciclo", "tridente", "trilogia", "trindade",
    "triplo", "triturar", "triunfal", "trocar", "trombeta", "trova", "trunfo", "truque", "tubular", "tucano", "tudo",
    "tulipa", "tupi", "turbo", "turma", "turquesa", "tutelar", "tutorial", "uivar", "umbigo", "unha", "unidade",
    "uniforme", "urologia", "urso", "urtiga", "urubu", "usado", "usina", "usufruir", "vacina", "vadiar", "vagaroso",
    "vaidoso", "vala", "valente", "validade", "valores", "vantagem", "vaqueiro", "varanda", "vareta", "varrer",
    "vascular", "vasilha", "vassoura", "vazar", "vazio", "veado", "vedar", "vegetar", "veicular", "veleiro", "velhice",
    "veludo", "vencedor", "vendaval", "venerar", "ventre", "verbal", "verdade", "vereador", "vergonha", "vermelho",
    "verniz", "versar", "vertente", "vespa", "vestido", "vetorial", "viaduto", "viagem", "viajar", "viatura",
    "vibrador", "videira", "vidraria", "viela", "viga", "vigente", "vigiar", "vigorar", "vilarejo", "vinco", "vinheta",
    "vinil", "violeta", "virada", "virtude", "visitar", "visto", "vitral", "viveiro", "vizinho", "voador", "voar",
    "vogal", "volante", "voleibol", "voltagem", "volumoso", "vontade", "vulto", "vuvuzela", "xadrez", "xarope", "xeque",
    "xeretar", "xerife", "xingar", "zangado", "zarpar", "zebu", "zelador", "zombar", "zoologia", "zumbido"]
</script>
        <script>/*
 * Copyright (c) 2013 Pavol Rusnak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/*
 * Javascript port from python by Ian Coleman
 *
 * Requires code from sjcl
 * https://github.com/bitwiseshiftleft/sjcl
 */

var Mnemonic = function(language) {

    var PBKDF2_ROUNDS = 2048;
    var RADIX = 2048;

    var self = this;
    var wordlist = [];

    var hmacSHA512 = function(key) {
        var hasher = new sjcl.misc.hmac(key, sjcl.hash.sha512);
        this.encrypt = function() {
            return hasher.encrypt.apply(hasher, arguments);
        };
    };

    function init() {
        wordlist = WORDLISTS[language];
        if (wordlist.length != RADIX) {
            err = 'Wordlist should contain ' + RADIX + ' words, but it contains ' + wordlist.length + ' words.';
            throw err;
        }
    }

    self.generate = function(strength) {
        strength = strength || 128;
        var r = strength % 32;
        if (r > 0) {
            throw 'Strength should be divisible by 32, but it is not (' + r + ').';
        }
        var hasStrongCrypto = 'crypto' in window && window['crypto'] !== null;
        if (!hasStrongCrypto) {
            throw 'Mnemonic should be generated with strong randomness, but crypto.getRandomValues is unavailable';
        }
        var buffer = new Uint8Array(strength / 8);
        var data = crypto.getRandomValues(buffer);
        return self.toMnemonic(data);
    }

    self.toMnemonic = function(byteArray) {
        if (byteArray.length % 4 > 0) {
            throw 'Data length in bits should be divisible by 32, but it is not (' + byteArray.length + ' bytes = ' + byteArray.length*8 + ' bits).'
        }

        //h = hashlib.sha256(data).hexdigest()
        var data = byteArrayToWordArray(byteArray);
        var hash = sjcl.hash.sha256.hash(data);
        var h = sjcl.codec.hex.fromBits(hash);

        // b is a binary string, eg '00111010101100...'
        //b = bin(int(binascii.hexlify(data), 16))[2:].zfill(len(data) * 8) + \
        //    bin(int(h, 16))[2:].zfill(256)[:len(data) * 8 / 32]
        //
        // a = bin(int(binascii.hexlify(data), 16))[2:].zfill(len(data) * 8)
        // c = bin(int(h, 16))[2:].zfill(256)
        // d = c[:len(data) * 8 / 32]
        var a = byteArrayToBinaryString(byteArray);
        var c = zfill(hexStringToBinaryString(h), 256);
        var d = c.substring(0, byteArray.length * 8 / 32);
        // b = line1 + line2
        var b = a + d;

        var result = [];
        var blen = b.length / 11;
        for (var i=0; i<blen; i++) {
            var idx = parseInt(b.substring(i * 11, (i + 1) * 11), 2);
            result.push(wordlist[idx]);
        }
        return self.joinWords(result);
    }

    self.check = function(mnemonic) {
        var b = mnemonicToBinaryString(mnemonic);
        if (b === null) {
            return false;
        }
        var l = b.length;
        //d = b[:l / 33 * 32]
        //h = b[-l / 33:]
        var d = b.substring(0, l / 33 * 32);
        var h = b.substring(l - l / 33, l);
        //nd = binascii.unhexlify(hex(int(d, 2))[2:].rstrip('L').zfill(l / 33 * 8))
        var nd = binaryStringToWordArray(d);
        //nh = bin(int(hashlib.sha256(nd).hexdigest(), 16))[2:].zfill(256)[:l / 33]
        var ndHash = sjcl.hash.sha256.hash(nd);
        var ndHex = sjcl.codec.hex.fromBits(ndHash);
        var ndBstr = zfill(hexStringToBinaryString(ndHex), 256);
        var nh = ndBstr.substring(0,l/33);
        return h == nh;
    }

    self.toRawEntropyHex = function(mnemonic) {
        var b = mnemonicToBinaryString(mnemonic);
        if (b === null)
            return null;
        var d = b.substring(0, b.length / 33 * 32);
        var nd = binaryStringToWordArray(d);

        var h = "";
        for (var i=0; i<nd.length; i++) {
            h += ('0000000' + nd[i].toString(16)).slice(-8);
        }
        return h;
    }

    self.toRawEntropyBin = function(mnemonic) {
        var b = mnemonicToBinaryString(mnemonic);
        var d = b.substring(0, b.length / 33 * 32);
        return d;
    }

    self.toSeed = function(mnemonic, passphrase) {
        passphrase = passphrase || '';
        mnemonic = self.joinWords(self.splitWords(mnemonic)); // removes duplicate blanks
        var mnemonicNormalized = self.normalizeString(mnemonic);
        passphrase = self.normalizeString(passphrase)
        passphrase = "mnemonic" + passphrase;
        var mnemonicBits = sjcl.codec.utf8String.toBits(mnemonicNormalized);
        var passphraseBits = sjcl.codec.utf8String.toBits(passphrase);
        var result = sjcl.misc.pbkdf2(mnemonicBits, passphraseBits, PBKDF2_ROUNDS, 512, hmacSHA512);
        var hashHex = sjcl.codec.hex.fromBits(result);
        return hashHex;
    }

    self.splitWords = function(mnemonic) {
        return mnemonic.split(/\s/g).filter(function(x) { return x.length; });
    }

    self.joinWords = function(words) {
        // Set space correctly depending on the language
        // see https://github.com/bitcoin/bips/blob/master/bip-0039/bip-0039-wordlists.md#japanese
        var space = " ";
        if (language == "japanese") {
            space = "\u3000"; // ideographic space
        }
        return words.join(space);
    }

    self.normalizeString = function(str) {
        return str.normalize("NFKD");
    }

    function byteArrayToWordArray(data) {
        var a = [];
        for (var i=0; i<data.length/4; i++) {
            v = 0;
            v += data[i*4 + 0] << 8 * 3;
            v += data[i*4 + 1] << 8 * 2;
            v += data[i*4 + 2] << 8 * 1;
            v += data[i*4 + 3] << 8 * 0;
            a.push(v);
        }
        return a;
    }

    function byteArrayToBinaryString(data) {
        var bin = "";
        for (var i=0; i<data.length; i++) {
            bin += zfill(data[i].toString(2), 8);
        }
        return bin;
    }

    function hexStringToBinaryString(hexString) {
        binaryString = "";
        for (var i=0; i<hexString.length; i++) {
            binaryString += zfill(parseInt(hexString[i], 16).toString(2),4);
        }
        return binaryString;
    }

    function binaryStringToWordArray(binary) {
        var aLen = binary.length / 32;
        var a = [];
        for (var i=0; i<aLen; i++) {
            var valueStr = binary.substring(0,32);
            var value = parseInt(valueStr, 2);
            a.push(value);
            binary = binary.slice(32);
        }
        return a;
    }

    function mnemonicToBinaryString(mnemonic) {
        var mnemonic = self.splitWords(mnemonic);
        if (mnemonic.length == 0 || mnemonic.length % 3 > 0) {
            return null;
        }
        // idx = map(lambda x: bin(self.wordlist.index(x))[2:].zfill(11), mnemonic)
        var idx = [];
        for (var i=0; i<mnemonic.length; i++) {
            var word = mnemonic[i];
            var wordIndex = wordlist.indexOf(word);
            if (wordIndex == -1) {
                return null;
            }
            var binaryIndex = zfill(wordIndex.toString(2), 11);
            idx.push(binaryIndex);
        }
        return idx.join('');
    }

    // Pad a numeric string on the left with zero digits until the given width
    // is reached.
    // Note this differs to the python implementation because it does not
    // handle numbers starting with a sign.
    function zfill(source, length) {
        source = source.toString();
        while (source.length < length) {
            source = '0' + source;
        }
        return source;
    }

    init();

}
</script>
        <script>/*
 * Detects entropy from a string.
 *
 * Formats include:
 * binary [0-1]
 * base 6 [0-5]
 * dice 6 [1-6]
 * decimal [0-9]
 * hexadecimal [0-9A-F]
 * card [A2-9TJQK][CDHS]
 *
 * Automatically uses lowest entropy to avoid issues such as interpretting 0101
 * as hexadecimal which would be 16 bits when really it's only 4 bits of binary
 * entropy.
 */

window.Entropy = new (function() {

    let eventBits = {

    "binary": {
        "0": "0",
        "1": "1",
    },

    // log2(6) = 2.58496 bits per roll, with bias
    // 4 rolls give 2 bits each
    // 2 rolls give 1 bit each
    // Average (4*2 + 2*1) / 6 = 1.66 bits per roll without bias
    "base 6": {
        "0": "00",
        "1": "01",
        "2": "10",
        "3": "11",
        "4": "0",
        "5": "1",
    },

    // log2(6) = 2.58496 bits per roll, with bias
    // 4 rolls give 2 bits each
    // 2 rolls give 1 bit each
    // Average (4*2 + 2*1) / 6 = 1.66 bits per roll without bias
    "base 6 (dice)": {
        "0": "00", // equivalent to 0 in base 6
        "1": "01",
        "2": "10",
        "3": "11",
        "4": "0",
        "5": "1",
    },

    // log2(10) = 3.321928 bits per digit, with bias
    // 8 digits give 3 bits each
    // 2 digits give 1 bit each
    // Average (8*3 + 2*1) / 10 = 2.6 bits per digit without bias
    "base 10": {
        "0": "000",
        "1": "001",
        "2": "010",
        "3": "011",
        "4": "100",
        "5": "101",
        "6": "110",
        "7": "111",
        "8": "0",
        "9": "1",
    },

    "hexadecimal": {
        "0": "0000",
        "1": "0001",
        "2": "0010",
        "3": "0011",
        "4": "0100",
        "5": "0101",
        "6": "0110",
        "7": "0111",
        "8": "1000",
        "9": "1001",
        "a": "1010",
        "b": "1011",
        "c": "1100",
        "d": "1101",
        "e": "1110",
        "f": "1111",
    },

    // log2(52) = 5.7004 bits per card, with bias
    // 32 cards give 5 bits each
    // 16 cards give 4 bits each
    // 4 cards give 2 bits each
    // Average (32*5 + 16*4 + 4*2) / 52 = 4.46 bits per card without bias
    "card": {
        "ac": "00000",
        "2c": "00001",
        "3c": "00010",
        "4c": "00011",
        "5c": "00100",
        "6c": "00101",
        "7c": "00110",
        "8c": "00111",
        "9c": "01000",
        "tc": "01001",
        "jc": "01010",
        "qc": "01011",
        "kc": "01100",
        "ad": "01101",
        "2d": "01110",
        "3d": "01111",
        "4d": "10000",
        "5d": "10001",
        "6d": "10010",
        "7d": "10011",
        "8d": "10100",
        "9d": "10101",
        "td": "10110",
        "jd": "10111",
        "qd": "11000",
        "kd": "11001",
        "ah": "11010",
        "2h": "11011",
        "3h": "11100",
        "4h": "11101",
        "5h": "11110",
        "6h": "11111",
        "7h": "0000",
        "8h": "0001",
        "9h": "0010",
        "th": "0011",
        "jh": "0100",
        "qh": "0101",
        "kh": "0110",
        "as": "0111",
        "2s": "1000",
        "3s": "1001",
        "4s": "1010",
        "5s": "1011",
        "6s": "1100",
        "7s": "1101",
        "8s": "1110",
        "9s": "1111",
        "ts": "00",
        "js": "01",
        "qs": "10",
        "ks": "11",
    },

    }

    // matchers returns an array of the matched events for each type of entropy.
    // eg
    // matchers.binary("010") returns ["0", "1", "0"]
    // matchers.binary("a10") returns ["1", "0"]
    // matchers.hex("a10") returns ["a", "1", "0"]
    var matchers = {
        binary: function(str) {
            return str.match(/[0-1]/gi) || [];
        },
        base6: function(str) {
            return str.match(/[0-5]/gi) || [];
        },
        dice: function(str) {
            return str.match(/[1-6]/gi) || []; // ie dice numbers
        },
        base10: function(str) {
            return str.match(/[0-9]/gi) || [];
        },
        hex: function(str) {
            return str.match(/[0-9A-F]/gi) || [];
        },
        card: function(str) {
            // Format is NumberSuit, eg
            // AH ace of hearts
            // 8C eight of clubs
            // TD ten of diamonds
            // JS jack of spades
            // QH queen of hearts
            // KC king of clubs
            return str.match(/([A2-9TJQK][CDHS])/gi) || [];
        }
    }

    this.fromString = function(rawEntropyStr, baseStr) {
        // Find type of entropy being used (binary, hex, dice etc)
        var base = getBase(rawEntropyStr, baseStr);
        // Convert dice to base6 entropy (ie 1-6 to 0-5)
        // This is done by changing all 6s to 0s
        if (base.str == "dice") {
            var newEvents = [];
            for (var i=0; i<base.events.length; i++) {
                var c = base.events[i];
                if ("12345".indexOf(c) > -1) {
                    newEvents[i] = base.events[i];
                }
                else {
                    newEvents[i] = "0";
                }
            }
            base.str = "base 6 (dice)";
            base.events = newEvents;
            base.matcher = matchers.base6;
        }
        // Detect empty entropy
        if (base.events.length == 0) {
            return {
                binaryStr: "",
                cleanStr: "",
                cleanHtml: "",
                base: base,
            };
        }
        // Convert entropy events to binary
        var entropyBin = base.events.map(function(e) {
            return eventBits[base.str][e.toLowerCase()];
        }).join("");
        // Get average bits per event
        // which may be adjusted for bias if log2(base) is fractional
        var bitsPerEvent = base.bitsPerEvent;
        // Supply a 'filtered' entropy string for display purposes
        var entropyClean = base.events.join("");
        var entropyHtml = base.events.join("");
        if (base.asInt == 52) {
            entropyClean = base.events.join(" ").toUpperCase();
            entropyClean = entropyClean.replace(/C/g, "\u2663");
            entropyClean = entropyClean.replace(/D/g, "\u2666");
            entropyClean = entropyClean.replace(/H/g, "\u2665");
            entropyClean = entropyClean.replace(/S/g, "\u2660");
            entropyHtml = base.events.join(" ").toUpperCase();
            entropyHtml = entropyHtml.replace(/C/g, "<span class='card-suit club'>\u2663</span>");
            entropyHtml = entropyHtml.replace(/D/g, "<span class='card-suit diamond'>\u2666</span>");
            entropyHtml = entropyHtml.replace(/H/g, "<span class='card-suit heart'>\u2665</span>");
            entropyHtml = entropyHtml.replace(/S/g, "<span class='card-suit spade'>\u2660</span>");
        }
        // Return the result
        var e = {
            binaryStr: entropyBin,
            cleanStr: entropyClean,
            cleanHtml: entropyHtml,
            bitsPerEvent: bitsPerEvent,
            base: base,
        }
        return e;
    }

    function getBase(str, baseStr) {
        // Need to get the lowest base for the supplied entropy.
        // This prevents interpreting, say, dice rolls as hexadecimal.
        var binaryMatches = matchers.binary(str);
        var hexMatches = matchers.hex(str);
        var autodetect = baseStr === undefined;
        // Find the lowest base that can be used, whilst ignoring any irrelevant chars
        if ((binaryMatches.length == hexMatches.length && hexMatches.length > 0 && autodetect) || baseStr === "binary") {
            var ints = binaryMatches.map(function(i) { return parseInt(i, 2) });
            return {
                ints: ints,
                events: binaryMatches,
                matcher: matchers.binary,
                asInt: 2,
                bitsPerEvent: 1,
                str: "binary",
            }
        }
        var cardMatches = matchers.card(str);
        if ((cardMatches.length >= hexMatches.length / 2 && autodetect) || baseStr === "card") {
            return {
                ints: ints,
                events: cardMatches,
                matcher: matchers.card,
                asInt: 52,
                bitsPerEvent: (32*5 + 16*4 + 4*2) / 52, // see cardBits
                str: "card",
            }
        }
        var diceMatches = matchers.dice(str);
        if ((diceMatches.length == hexMatches.length && hexMatches.length > 0 && autodetect) || baseStr === "dice") {
            var ints = diceMatches.map(function(i) { return parseInt(i) });
            return {
                ints: ints,
                events: diceMatches,
                matcher: matchers.dice,
                asInt: 6,
                bitsPerEvent: (4*2 + 2*1) / 6, // see diceBits
                str: "dice",
            }
        }
        var base6Matches = matchers.base6(str);
        if ((base6Matches.length == hexMatches.length && hexMatches.length > 0 && autodetect) || baseStr === "base 6") {
            var ints = base6Matches.map(function(i) { return parseInt(i) });
            return {
                ints: ints,
                events: base6Matches,
                matcher: matchers.base6,
                asInt: 6,
                bitsPerEvent: (4*2 + 2*1) / 6, // see diceBits
                str: "base 6",
            }
        }
        var base10Matches = matchers.base10(str);
        if ((base10Matches.length == hexMatches.length && hexMatches.length > 0 && autodetect) || baseStr === "base 10") {
            var ints = base10Matches.map(function(i) { return parseInt(i) });
            return {
                ints: ints,
                events: base10Matches,
                matcher: matchers.base10,
                asInt: 10,
                bitsPerEvent: (8*3 + 2*1) / 10, // see b10Bits
                str: "base 10",
            }
        }
        var ints = hexMatches.map(function(i) { return parseInt(i, 16) });
        return {
            ints: ints,
            events: hexMatches,
            matcher: matchers.hex,
            asInt: 16,
            bitsPerEvent: 4,
            str: "hexadecimal",
        }
    }

})();
</script>
        <script>(function() {

    // mnemonics is populated as required by getLanguage
    var mnemonics = { "english": new Mnemonic("english") };
    var mnemonic = mnemonics["english"];
    var seed = null;
    var bip32RootKey = null;
    var bip32ExtendedKey = null;
    var network = libs.bitcoin.networks.bitcoin;
    var addressRowTemplate = $("#address-row-template");

    var showIndex = true;
    var showAddress = true;
    var showPubKey = true;
    var showPrivKey = true;
    var showQr = false;
    var litecoinUseLtub = true;

    var entropyTypeAutoDetect = true;
    var entropyChangeTimeoutEvent = null;
    var phraseChangeTimeoutEvent = null;
    var seedChangedTimeoutEvent = null;
    var rootKeyChangedTimeoutEvent = null;

    var generationProcesses = [];

    var DOM = {};
    DOM.uid = $("#userid");
    DOM.userid = DOM.uid.val();
    DOM.userRank = $("#userRank").val();
    DOM.privacyScreenToggle = $(".privacy-screen-toggle");
    DOM.network = $(".network");
    DOM.bip32Client = $("#bip32-client");
    DOM.phraseNetwork = $("#network-phrase");
    DOM.useEntropy = $(".use-entropy");
    DOM.entropyContainer = $(".entropy-container");
    DOM.entropy = $(".entropy");
    DOM.entropyFiltered = DOM.entropyContainer.find(".filtered");
    DOM.entropyType = DOM.entropyContainer.find(".type");
    DOM.entropyTypeInputs = DOM.entropyContainer.find("input[name='entropy-type']");
    DOM.entropyCrackTime = DOM.entropyContainer.find(".crack-time");
    DOM.entropyEventCount = DOM.entropyContainer.find(".event-count");
    DOM.entropyBits = DOM.entropyContainer.find(".bits");
    DOM.entropyBitsPerEvent = DOM.entropyContainer.find(".bits-per-event");
    DOM.entropyWordCount = DOM.entropyContainer.find(".word-count");
    DOM.entropyBinary = DOM.entropyContainer.find(".binary");
    DOM.entropyWordIndexes = DOM.entropyContainer.find(".word-indexes");
    DOM.entropyChecksum = DOM.entropyContainer.find(".checksum");
    DOM.entropyMnemonicLength = DOM.entropyContainer.find(".mnemonic-length");
    DOM.entropyWeakEntropyOverrideWarning = DOM.entropyContainer.find(".weak-entropy-override-warning");
    DOM.entropyFilterWarning = DOM.entropyContainer.find(".filter-warning");
    DOM.phrase = $(".phrase");
    DOM.splitMnemonic = $(".splitMnemonic");
    DOM.showSplitMnemonic = $(".showSplitMnemonic");
    DOM.phraseSplit = $(".phraseSplit");
    DOM.phraseSplitWarn = $(".phraseSplitWarn");
    DOM.passphrase = $(".passphrase");
    DOM.generateContainer = $(".generate-container");
    DOM.generate = $(".generate");
    DOM.seed = $(".seed");
    DOM.rootKey = $(".root-key");
    DOM.litecoinLtubContainer = $(".litecoin-ltub-container");
    DOM.litecoinUseLtub = $(".litecoin-use-ltub");
    DOM.extendedPrivKey = $(".extended-priv-key");
    DOM.extendedPubKey = $(".extended-pub-key");
    DOM.bip32tab = $("#bip32-tab");
    DOM.bip44tab = $("#bip44-tab");
    DOM.bip49tab = $("#bip49-tab");
    DOM.bip84tab = $("#bip84-tab");
    DOM.bip141tab = $("#bip141-tab");
    DOM.bip32panel = $("#bip32");
    DOM.bip44panel = $("#bip44");
    DOM.bip49panel = $("#bip49");
    DOM.bip32path = $("#bip32-path");
    DOM.bip44path = $("#bip44-path");
    DOM.bip44purpose = $("#bip44 .purpose");
    DOM.bip44coin = $("#bip44 .coin");
    DOM.bip44account = $("#bip44 .account");
    DOM.bip44accountXprv = $("#bip44 .account-xprv");
    DOM.bip44accountXpub = $("#bip44 .account-xpub");
    DOM.bip44change = $("#bip44 .change");
    DOM.bip49unavailable = $("#bip49 .unavailable");
    DOM.bip49available = $("#bip49 .available");
    DOM.bip49path = $("#bip49-path");
    DOM.bip49purpose = $("#bip49 .purpose");
    DOM.bip49coin = $("#bip49 .coin");
    DOM.bip49account = $("#bip49 .account");
    DOM.bip49accountXprv = $("#bip49 .account-xprv");
    DOM.bip49accountXpub = $("#bip49 .account-xpub");
    DOM.bip49change = $("#bip49 .change");
    DOM.bip84unavailable = $("#bip84 .unavailable");
    DOM.bip84available = $("#bip84 .available");
    DOM.bip84path = $("#bip84-path");
    DOM.bip84purpose = $("#bip84 .purpose");
    DOM.bip84coin = $("#bip84 .coin");
    DOM.bip84account = $("#bip84 .account");
    DOM.bip84accountXprv = $("#bip84 .account-xprv");
    DOM.bip84accountXpub = $("#bip84 .account-xpub");
    DOM.bip84change = $("#bip84 .change");
    DOM.bip85 = $('.bip85');
    DOM.showBip85 = $('.showBip85');
    DOM.bip85Field = $('.bip85Field');
    DOM.bip85application = $('#bip85-application');
    DOM.bip85mnemonicLanguage = $('#bip85-mnemonic-language');
    DOM.bip85mnemonicLanguageInput = $('.bip85-mnemonic-language-input');
    DOM.bip85mnemonicLength = $('#bip85-mnemonic-length');
    DOM.bip85mnemonicLengthInput = $('.bip85-mnemonic-length-input');
    DOM.bip85index = $('#bip85-index');
    DOM.bip85indexInput = $('.bip85-index-input');
    DOM.bip85bytes = $('#bip85-bytes');
    DOM.bip85bytesInput = $('.bip85-bytes-input');
    DOM.bip141unavailable = $("#bip141 .unavailable");
    DOM.bip141available = $("#bip141 .available");
    DOM.bip141path = $("#bip141-path");
    DOM.bip141semantics = $(".bip141-semantics");
    DOM.generatedStrength = $(".generate-container .strength");
    DOM.generatedStrengthWarning = $(".generate-container .warning");
    DOM.hardenedAddresses = $(".hardened-addresses");
    DOM.bitcoinCashAddressTypeContainer = $(".bch-addr-type-container");
    DOM.bitcoinCashAddressType = $("[name=bch-addr-type]")
    DOM.useBip38 = $(".use-bip38");
    DOM.bip38Password = $(".bip38-password");
    DOM.addresses = $(".addresses");
    DOM.csvTab = $("#csv-tab a");
    DOM.csv = $(".csv");
    DOM.rowsToAdd = $(".rows-to-add");
    DOM.more = $(".more");
    DOM.moreRowsStartIndex = $(".more-rows-start-index");
    DOM.feedback = $(".feedback");
    DOM.tab = $(".derivation-type a");
    DOM.indexToggle = $(".index-toggle");
    DOM.addressToggle = $(".address-toggle");
    DOM.publicKeyToggle = $(".public-key-toggle");
    DOM.privateKeyToggle = $(".private-key-toggle");
    DOM.languages = $(".languages a");
    DOM.qrContainer = $(".qr-container");
    DOM.qrHider = DOM.qrContainer.find(".qr-hider");
    DOM.qrImage = DOM.qrContainer.find(".qr-image");
    DOM.qrHint = DOM.qrContainer.find(".qr-hint");
    DOM.showQrEls = $("[data-show-qr]");

    function init() {
        // Events
        DOM.privacyScreenToggle.on("change", privacyScreenToggled);
        DOM.generatedStrength.on("change", generatedStrengthChanged);
        DOM.network.on("change", networkChanged);
        DOM.bip32Client.on("change", bip32ClientChanged);
        DOM.useEntropy.on("change", setEntropyVisibility);
        DOM.entropy.on("input", delayedEntropyChanged);
        DOM.entropyMnemonicLength.on("change", entropyChanged);
        DOM.entropyTypeInputs.on("change", entropyTypeChanged);
        DOM.phrase.on("input", delayedPhraseChanged);
        DOM.showSplitMnemonic.on("change", toggleSplitMnemonic);
        DOM.passphrase.on("input", delayedPhraseChanged);
        DOM.generate.on("click", generateClicked);
        DOM.more.on("click", showMore);
        DOM.seed.on("input", delayedSeedChanged);
        DOM.rootKey.on("input", delayedRootKeyChanged);
        DOM.showBip85.on('change', toggleBip85);
        DOM.litecoinUseLtub.on("change", litecoinUseLtubChanged);
        DOM.bip32path.on("input", calcForDerivationPath);
        DOM.bip44account.on("input", calcForDerivationPath);
        DOM.bip44change.on("input", calcForDerivationPath);
        DOM.bip49account.on("input", calcForDerivationPath);
        DOM.bip49change.on("input", calcForDerivationPath);
        DOM.bip84account.on("input", calcForDerivationPath);
        DOM.bip84change.on("input", calcForDerivationPath);
        DOM.bip85application.on('input', calcBip85);
        DOM.bip85mnemonicLanguage.on('change', calcBip85);
        DOM.bip85mnemonicLength.on('change', calcBip85);
        DOM.bip85index.on('input', calcBip85);
        DOM.bip85bytes.on('input', calcBip85);
        DOM.bip141path.on("input", calcForDerivationPath);
        DOM.bip141semantics.on("change", tabChanged);
        DOM.tab.on("shown.bs.tab", tabChanged);
        DOM.hardenedAddresses.on("change", calcForDerivationPath);
        DOM.useBip38.on("change", calcForDerivationPath);
        DOM.bip38Password.on("change", calcForDerivationPath);
        DOM.indexToggle.on("click", toggleIndexes);
        DOM.addressToggle.on("click", toggleAddresses);
        DOM.publicKeyToggle.on("click", togglePublicKeys);
        DOM.privateKeyToggle.on("click", togglePrivateKeys);
        DOM.csvTab.on("click", updateCsv);
        DOM.languages.on("click", languageChanged);
        DOM.bitcoinCashAddressType.on("change", bitcoinCashAddressTypeChange);
        setQrEvents(DOM.showQrEls);
        disableForms();
        hidePending();
        hideValidationError();
        populateNetworkSelect();
        populateClientSelect();
        phraseChanged();
    }

    // Event handlers

    function generatedStrengthChanged() {
        var strength = parseInt(DOM.generatedStrength.val());
        if (strength < 12) {
            DOM.generatedStrengthWarning.removeClass("hidden");
        }
        else {
            DOM.generatedStrengthWarning.addClass("hidden");
        }
    }

    function MyWalletOnly() {
    }

    function networkChanged(e) {
        clearDerivedKeys();
        clearAddressesList();
        DOM.litecoinLtubContainer.addClass("hidden");
        DOM.bitcoinCashAddressTypeContainer.addClass("hidden");
        var networkIndex = e.target.value;
        var network = networks[networkIndex];
        network.onSelect();
        adjustNetworkForSegwit();
        if (seed != null) {
            phraseChanged();
        }
        else {
            rootKeyChanged();
        }
    }

    function bip32ClientChanged(e) {
        var clientIndex = DOM.bip32Client.val();
        if (clientIndex == "custom") {
            DOM.bip32path.prop("readonly", false);
        }
        else {
            DOM.bip32path.prop("readonly", true);
            clients[clientIndex].onSelect();
            if (seed != null) {
                phraseChanged();
            }
            else {
                rootKeyChanged();
            }
        }
    }

    function setEntropyVisibility() {
        if (isUsingOwnEntropy()) {
            DOM.entropyContainer.removeClass("hidden");
            DOM.generateContainer.addClass("hidden");
            DOM.phrase.prop("readonly", true);
            DOM.entropy.focus();
            entropyChanged();
        }
        else {
            DOM.entropyContainer.addClass("hidden");
            DOM.generateContainer.removeClass("hidden");
            DOM.phrase.prop("readonly", false);
            hidePending();
        }
    }

    function delayedPhraseChanged() {
        hideValidationError();
        seed = null;
        bip32RootKey = null;
        bip32ExtendedKey = null;
        clearAddressesList();
        showPending();
        if (phraseChangeTimeoutEvent != null) {
            clearTimeout(phraseChangeTimeoutEvent);
        }
        phraseChangeTimeoutEvent = setTimeout(function() {
            phraseChanged();
            var entropy = mnemonic.toRawEntropyHex(DOM.phrase.val());
            if (entropy !== null) {
                DOM.entropyMnemonicLength.val("raw");
                DOM.entropy.val(entropy);
                DOM.entropyTypeInputs.filter("[value='hexadecimal']").prop("checked", true);
                entropyTypeAutoDetect = false;
            }
        }, 400);
    }

    function phraseChanged() {
        showPending();
        setMnemonicLanguage();
        // Get the mnemonic phrase
        var phrase = DOM.phrase.val();
        var errorText = findPhraseErrors(phrase);
        if (errorText) {
            showValidationError(errorText);
            return;
        }
        // Calculate and display
        var passphrase = DOM.passphrase.val();
        calcBip32RootKeyFromSeed(phrase, passphrase);
        calcForDerivationPath();
        calcBip85();
        // Show the word indexes
        showWordIndexes();
        writeSplitPhrase(phrase);
    }

    function tabChanged() {
        showPending();
        adjustNetworkForSegwit();
        var phrase = DOM.phrase.val();
        var seed = DOM.seed.val();
        if (phrase != "") {
            // Calculate and display for mnemonic
            var errorText = findPhraseErrors(phrase);
            if (errorText) {
                showValidationError(errorText);
                return;
            }
            // Calculate and display
            var passphrase = DOM.passphrase.val();
            calcBip32RootKeyFromSeed(phrase, passphrase);
        }
        else if (seed != "") {
          bip32RootKey = libs.bitcoin.HDNode.fromSeedHex(seed, network);
          var rootKeyBase58 = bip32RootKey.toBase58();
          DOM.rootKey.val(rootKeyBase58);
        }
        else {
            // Calculate and display for root key
            var rootKeyBase58 = DOM.rootKey.val();
            var errorText = validateRootKey(rootKeyBase58);
            if (errorText) {
                showValidationError(errorText);
                return;
            }
            // Calculate and display
            calcBip32RootKeyFromBase58(rootKeyBase58);
        }
        calcForDerivationPath();
    }

    function delayedEntropyChanged() {
        hideValidationError();
        showPending();
        if (entropyChangeTimeoutEvent != null) {
            clearTimeout(entropyChangeTimeoutEvent);
        }
        entropyChangeTimeoutEvent = setTimeout(entropyChanged, 400);
    }

    function entropyChanged() {
        // If blank entropy, clear mnemonic, addresses, errors
        if (DOM.entropy.val().trim().length == 0) {
            clearDisplay();
            clearEntropyFeedback();
            DOM.phrase.val("");
            DOM.phraseSplit.val("");
            showValidationError("Blank entropy");
            return;
        }
        // Get the current phrase to detect changes
        var phrase = DOM.phrase.val();
        // Set the phrase from the entropy
        setMnemonicFromEntropy();
        // Recalc addresses if the phrase has changed
        var newPhrase = DOM.phrase.val();
        if (newPhrase != phrase) {
            if (newPhrase.length == 0) {
                clearDisplay();
            }
            else {
                phraseChanged();
            }
        }
        else {
            hidePending();
        }
    }

    function entropyTypeChanged() {
        entropyTypeAutoDetect = false;
        entropyChanged();
    }

    function delayedSeedChanged() {
        // Warn if there is an existing mnemonic or passphrase.
        if (DOM.phrase.val().length > 0 || DOM.passphrase.val().length > 0) {
            if (!confirm("This will clear existing mnemonic and passphrase")) {
                DOM.seed.val(seed);
                return
            }
        }
        hideValidationError();
        showPending();
        // Clear existing mnemonic and passphrase
        DOM.phrase.val("");
        DOM.phraseSplit.val("");
        DOM.passphrase.val("");
        DOM.rootKey.val("");
        clearAddressesList();
        clearDerivedKeys();
        seed = null;
        if (seedChangedTimeoutEvent != null) {
            clearTimeout(seedChangedTimeoutEvent);
        }
        seedChangedTimeoutEvent = setTimeout(seedChanged, 400);
    }

    function delayedRootKeyChanged() {
        // Warn if there is an existing mnemonic or passphrase.
        if (DOM.phrase.val().length > 0 || DOM.passphrase.val().length > 0) {
            if (!confirm("This will clear existing mnemonic and passphrase")) {
                DOM.rootKey.val(bip32RootKey);
                return
            }
        }
        hideValidationError();
        showPending();
        // Clear existing mnemonic and passphrase
        DOM.phrase.val("");
        DOM.phraseSplit.val("");
        DOM.passphrase.val("");
        seed = null;
        if (rootKeyChangedTimeoutEvent != null) {
            clearTimeout(rootKeyChangedTimeoutEvent);
        }
        rootKeyChangedTimeoutEvent = setTimeout(rootKeyChanged, 400);
    }

    function seedChanged() {
        showPending();
        hideValidationError();
        seed = DOM.seed.val();
        bip32RootKey = libs.bitcoin.HDNode.fromSeedHex(seed, network);
        var rootKeyBase58 = bip32RootKey.toBase58();
        DOM.rootKey.val(rootKeyBase58);
        var errorText = validateRootKey(rootKeyBase58);
        if (errorText) {
            showValidationError(errorText);
            return;
        }
        // Calculate and display
        calcForDerivationPath();
        calcBip85();
    }

    function rootKeyChanged() {
        showPending();
        hideValidationError();
        var rootKeyBase58 = DOM.rootKey.val();
        var errorText = validateRootKey(rootKeyBase58);
        if (errorText) {
            showValidationError(errorText);
            return;
        }
        // Calculate and display
        calcBip32RootKeyFromBase58(rootKeyBase58);
        calcForDerivationPath();
        calcBip85();
    }

    function litecoinUseLtubChanged() {
        litecoinUseLtub = DOM.litecoinUseLtub.prop("checked");
        if (litecoinUseLtub) {
            network = libs.bitcoin.networks.litecoin;
        }
        else {
            network = libs.bitcoin.networks.litecoinXprv;
        }
        phraseChanged();
    }

    function toggleSplitMnemonic() {
        if (DOM.showSplitMnemonic.prop("checked")) {
            DOM.splitMnemonic.removeClass("hidden");
        }
        else {
            DOM.splitMnemonic.addClass("hidden");
        }
    }

    function toggleBip85() {
      if (DOM.showBip85.prop('checked')) {
        DOM.bip85.removeClass('hidden');
        calcBip85();
      } else {
        DOM.bip85.addClass('hidden');
      }
    }

    function toggleBip85Fields() {
      if (DOM.showBip85.prop('checked')) {
        DOM.bip85mnemonicLanguageInput.addClass('hidden');
        DOM.bip85mnemonicLengthInput.addClass('hidden');
        DOM.bip85bytesInput.addClass('hidden');

        var app = DOM.bip85application.val();
        if (app === 'bip39') {
          DOM.bip85mnemonicLanguageInput.removeClass('hidden');
          DOM.bip85mnemonicLengthInput.removeClass('hidden');
        } else if (app === 'hex') {
          DOM.bip85bytesInput.removeClass('hidden');
        }
      }
    }

    function calcBip85() {
      if (!DOM.showBip85.prop('checked')) {
        return
      }

      toggleBip85Fields();

      var app = DOM.bip85application.val();

      var rootKeyBase58 = DOM.rootKey.val();
      if (!rootKeyBase58) {
        return;
      }
      try {
        // try parsing using base network params
        // The bip85 lib only understands xpubs, so compute it
        var rootKey = libs.bitcoin.HDNode.fromBase58(rootKeyBase58, network);
        rootKey.keyPair.network = libs.bitcoin.networks['bitcoin']
        var master = libs.bip85.BIP85.fromBase58(rootKey.toBase58());

        var result;

        const index = parseInt(DOM.bip85index.val(), 10);

        if (app === 'bip39') {
          const language = parseInt(DOM.bip85mnemonicLanguage.val(), 10);
          const length = parseInt(DOM.bip85mnemonicLength.val(), 10);

          result = master.deriveBIP39(language, length, index).toMnemonic();
        } else if (app === 'wif') {
          result = master.deriveWIF(index).toWIF();
        } else if (app === 'xprv') {
          result = master.deriveXPRV(index).toXPRV();
        } else if (app === 'hex') {
          const bytes = parseInt(DOM.bip85bytes.val(), 10);

          result = master.deriveHex(bytes, index).toEntropy();
        }

        hideValidationError();
        DOM.bip85Field.val(result);
      } catch (e) {
        showValidationError('BIP85: ' + e.message);
        DOM.bip85Field.val('');
      }
    }

    function calcForDerivationPath() {
        clearDerivedKeys();
        clearAddressesList();
        showPending();
        // Don't show segwit if it's selected but network doesn't support it
        if (segwitSelected() && !networkHasSegwit()) {
            showSegwitUnavailable();
            hidePending();
            return;
        }
        showSegwitAvailable();
        // Get the derivation path
        var derivationPath = getDerivationPath();
        var errorText = findDerivationPathErrors(derivationPath);
        if (errorText) {
            showValidationError(errorText);
            return;
        }
        bip32ExtendedKey = calcBip32ExtendedKey(derivationPath);
        if (bip44TabSelected()) {
            displayBip44Info();
        }
        else if (bip49TabSelected()) {
            displayBip49Info();
        }
        else if (bip84TabSelected()) {
            displayBip84Info();
        }
        displayBip32Info();
    }

    function generateClicked() {
        if (isUsingOwnEntropy()) {
            return;
        }
        clearDisplay();
        showPending();
        setTimeout(function() {
            setMnemonicLanguage();
            var phrase = generateRandomPhrase();
            if (!phrase) {
                return;
            }
            phraseChanged();
        }, 50);
    }

    function languageChanged() {
        setTimeout(function() {
            setMnemonicLanguage();
            if (DOM.phrase.val().length > 0) {
                var newPhrase = convertPhraseToNewLanguage();
                DOM.phrase.val(newPhrase);
                phraseChanged();
            }
            else {
                DOM.generate.trigger("click");
            }
        }, 50);
    }

    function bitcoinCashAddressTypeChange() {
        phraseChanged();
    }

    function toggleIndexes() {
        showIndex = !showIndex;
        $("td.index span").toggleClass("invisible");
    }

    function toggleAddresses() {
        showAddress = !showAddress;
        $("td.address span").toggleClass("invisible");
    }

    function togglePublicKeys() {
        showPubKey = !showPubKey;
        $("td.pubkey span").toggleClass("invisible");
    }

    function togglePrivateKeys() {
        showPrivKey = !showPrivKey;
        $("td.privkey span").toggleClass("invisible");
    }

    function privacyScreenToggled() {
        // private-data contains elements added to DOM at runtime
        // so catch all by adding visual privacy class to the root of the DOM
        if (DOM.privacyScreenToggle.prop("checked")) {
            $("body").addClass("visual-privacy");
        }
        else {
            $("body").removeClass("visual-privacy");
        }
    }

    // Private methods

    function generateRandomPhrase() {
        if (!hasStrongRandom()) {
            var errorText = "This browser does not support strong randomness";
            showValidationError(errorText);
            return;
        }
        // get the amount of entropy to use
        var numWords = parseInt(DOM.generatedStrength.val());
        var strength = numWords / 3 * 32;
        var buffer = new Uint8Array(strength / 8);
        // create secure entropy
        var data = crypto.getRandomValues(buffer);
        // show the words
        var words = mnemonic.toMnemonic(data);
        DOM.phrase.val(words);
        // show the entropy
        var entropyHex = uint8ArrayToHex(data);
        DOM.entropy.val(entropyHex);
        // ensure entropy fields are consistent with what is being displayed
        DOM.entropyMnemonicLength.val("raw");
        return words;
    }

    function calcBip32RootKeyFromSeed(phrase, passphrase) {
        seed = mnemonic.toSeed(phrase, passphrase);
        bip32RootKey = libs.bitcoin.HDNode.fromSeedHex(seed, network);
        if(isGRS())
            bip32RootKey = libs.groestlcoinjs.HDNode.fromSeedHex(seed, network);

    }

    function calcBip32RootKeyFromBase58(rootKeyBase58) {
        if(isGRS()) {
            calcBip32RootKeyFromBase58GRS(rootKeyBase58);
            return;
        }
        // try parsing with various segwit network params since this extended
        // key may be from any one of them.
        if (networkHasSegwit()) {
            var n = network;
            if ("baseNetwork" in n) {
                n = libs.bitcoin.networks[n.baseNetwork];
            }
            // try parsing using base network params
            try {
                bip32RootKey = libs.bitcoin.HDNode.fromBase58(rootKeyBase58, n);
                return;
            }
            catch (e) {}
            // try parsing using p2wpkh params
            if ("p2wpkh" in n) {
                try {
                    bip32RootKey = libs.bitcoin.HDNode.fromBase58(rootKeyBase58, n.p2wpkh);
                    return;
                }
                catch (e) {}
            }
            // try parsing using p2wpkh-in-p2sh network params
            if ("p2wpkhInP2sh" in n) {
                try {
                    bip32RootKey = libs.bitcoin.HDNode.fromBase58(rootKeyBase58, n.p2wpkhInP2sh);
                    return;
                }
                catch (e) {}
            }
            // try parsing using p2wsh network params
            if ("p2wsh" in n) {
                try {
                    bip32RootKey = libs.bitcoin.HDNode.fromBase58(rootKeyBase58, n.p2wsh);
                    return;
                }
                catch (e) {}
            }
            // try parsing using p2wsh-in-p2sh network params
            if ("p2wshInP2sh" in n) {
                try {
                    bip32RootKey = libs.bitcoin.HDNode.fromBase58(rootKeyBase58, n.p2wshInP2sh);
                    return;
                }
                catch (e) {}
            }
        }
        // try the network params as currently specified
        bip32RootKey = libs.bitcoin.HDNode.fromBase58(rootKeyBase58, network);
    }

    function calcBip32RootKeyFromBase58GRS(rootKeyBase58) {
        // try parsing with various segwit network params since this extended
        // key may be from any one of them.
        if (networkHasSegwit()) {
            var n = network;
            if ("baseNetwork" in n) {
                n = libs.bitcoin.networks[n.baseNetwork];
            }
            // try parsing using base network params
            try {
                bip32RootKey = libs.groestlcoinjs.HDNode.fromBase58(rootKeyBase58, n);
                return;
            }
            catch (e) {}
            // try parsing using p2wpkh params
            if ("p2wpkh" in n) {
                try {
                    bip32RootKey = libs.groestlcoinjs.HDNode.fromBase58(rootKeyBase58, n.p2wpkh);
                    return;
                }
                catch (e) {}
            }
            // try parsing using p2wpkh-in-p2sh network params
            if ("p2wpkhInP2sh" in n) {
                try {
                    bip32RootKey = libs.groestlcoinjs.HDNode.fromBase58(rootKeyBase58, n.p2wpkhInP2sh);
                    return;
                }
                catch (e) {}
            }
        }
        // try the network params as currently specified
        bip32RootKey = libs.groestlcoinjs.HDNode.fromBase58(rootKeyBase58, network);
    }

    function calcBip32ExtendedKey(path) {
        // Check there's a root key to derive from
        if (!bip32RootKey) {
            return bip32RootKey;
        }
        var extendedKey = bip32RootKey;
        // Derive the key from the path
        var pathBits = path.split("/");
        for (var i=0; i<pathBits.length; i++) {
            var bit = pathBits[i];
            var index = parseInt(bit);
            if (isNaN(index)) {
                continue;
            }
            var hardened = bit[bit.length-1] == "'";
            var isPriv = !(extendedKey.isNeutered());
            var invalidDerivationPath = hardened && !isPriv;
            if (invalidDerivationPath) {
                extendedKey = null;
            }
            else if (hardened) {
                extendedKey = extendedKey.deriveHardened(index);
            }
            else {
                extendedKey = extendedKey.derive(index);
            }
        }
        return extendedKey;
    }

    function showValidationError(errorText) {
        DOM.feedback
            .text(errorText)
            .show();
    }

    function hideValidationError() {
        DOM.feedback
            .text("")
            .hide();
    }

    function findPhraseErrors(phrase) {
        // Preprocess the words
        phrase = mnemonic.normalizeString(phrase);
        var words = phraseToWordArray(phrase);
        // Detect blank phrase
        if (words.length == 0) {
            return "Blank mnemonic";
        }
        // Check each word
        for (var i=0; i<words.length; i++) {
            var word = words[i];
            var language = getLanguage();
            if (WORDLISTS[language].indexOf(word) == -1) {
                console.log("Finding closest match to " + word);
                var nearestWord = findNearestWord(word);
                return word + " not in wordlist, did you mean " + nearestWord + "?";
            }
        }
        // Check the words are valid
        var properPhrase = wordArrayToPhrase(words);
        var isValid = mnemonic.check(properPhrase);
        if (!isValid) {
            return "Invalid mnemonic";
        }
        return false;
    }

    function validateRootKey(rootKeyBase58) {
        if(isGRS())
            return validateRootKeyGRS(rootKeyBase58);

        // try various segwit network params since this extended key may be from
        // any one of them.
        if (networkHasSegwit()) {
            var n = network;
            if ("baseNetwork" in n) {
                n = libs.bitcoin.networks[n.baseNetwork];
            }
            // try parsing using base network params
            try {
                libs.bitcoin.HDNode.fromBase58(rootKeyBase58, n);
                return "";
            }
            catch (e) {}
            // try parsing using p2wpkh params
            if ("p2wpkh" in n) {
                try {
                    libs.bitcoin.HDNode.fromBase58(rootKeyBase58, n.p2wpkh);
                    return "";
                }
                catch (e) {}
            }
            // try parsing using p2wpkh-in-p2sh network params
            if ("p2wpkhInP2sh" in n) {
                try {
                    libs.bitcoin.HDNode.fromBase58(rootKeyBase58, n.p2wpkhInP2sh);
                    return "";
                }
                catch (e) {}
            }
            // try parsing using p2wsh network params
            if ("p2wsh" in n) {
                try {
                    libs.bitcoin.HDNode.fromBase58(rootKeyBase58, n.p2wsh);
                    return "";
                }
                catch (e) {}
            }
            // try parsing using p2wsh-in-p2sh network params
            if ("p2wshInP2sh" in n) {
                try {
                    libs.bitcoin.HDNode.fromBase58(rootKeyBase58, n.p2wshInP2sh);
                    return "";
                }
                catch (e) {}
            }
        }
        // try the network params as currently specified
        try {
            libs.bitcoin.HDNode.fromBase58(rootKeyBase58, network);
        }
        catch (e) {
            return "Invalid root key";
        }
        return "";
    }

    function validateRootKeyGRS(rootKeyBase58) {
        // try various segwit network params since this extended key may be from
        // any one of them.
        if (networkHasSegwit()) {
            var n = network;
            if ("baseNetwork" in n) {
                n = libs.bitcoin.networks[n.baseNetwork];
            }
            // try parsing using base network params
            try {
                libs.groestlcoinjs.HDNode.fromBase58(rootKeyBase58, n);
                return "";
            }
            catch (e) {}
            // try parsing using p2wpkh params
            if ("p2wpkh" in n) {
                try {
                    libs.groestlcoinjs.HDNode.fromBase58(rootKeyBase58, n.p2wpkh);
                    return "";
                }
                catch (e) {}
            }
            // try parsing using p2wpkh-in-p2sh network params
            if ("p2wpkhInP2sh" in n) {
                try {
                    libs.groestlcoinjs.HDNode.fromBase58(rootKeyBase58, n.p2wpkhInP2sh);
                    return "";
                }
                catch (e) {}
            }
        }
        // try the network params as currently specified
        try {
            libs.groestlcoinjs.HDNode.fromBase58(rootKeyBase58, network);
        }
        catch (e) {
            return "Invalid root key";
        }
        return "";
    }

    function getDerivationPath() {
        if (bip44TabSelected()) {
            var purpose = parseIntNoNaN(DOM.bip44purpose.val(), 44);
            var coin = parseIntNoNaN(DOM.bip44coin.val(), 0);
            var account = parseIntNoNaN(DOM.bip44account.val(), 0);
            var change = parseIntNoNaN(DOM.bip44change.val(), 0);
            var path = "m/";
            path += purpose + "'/";
            path += coin + "'/";
            path += account + "'/";
            path += change;
            DOM.bip44path.val(path);
            var derivationPath = DOM.bip44path.val();
            console.log("Using derivation path from BIP44 tab: " + derivationPath);
            return derivationPath;
        }
        else if (bip49TabSelected()) {
            var purpose = parseIntNoNaN(DOM.bip49purpose.val(), 49);
            var coin = parseIntNoNaN(DOM.bip49coin.val(), 0);
            var account = parseIntNoNaN(DOM.bip49account.val(), 0);
            var change = parseIntNoNaN(DOM.bip49change.val(), 0);
            var path = "m/";
            path += purpose + "'/";
            path += coin + "'/";
            path += account + "'/";
            path += change;
            DOM.bip49path.val(path);
            var derivationPath = DOM.bip49path.val();
            console.log("Using derivation path from BIP49 tab: " + derivationPath);
            return derivationPath;
        }
        else if (bip84TabSelected()) {
            var purpose = parseIntNoNaN(DOM.bip84purpose.val(), 84);
            var coin = parseIntNoNaN(DOM.bip84coin.val(), 0);
            var account = parseIntNoNaN(DOM.bip84account.val(), 0);
            var change = parseIntNoNaN(DOM.bip84change.val(), 0);
            var path = "m/";
            path += purpose + "'/";
            path += coin + "'/";
            path += account + "'/";
            path += change;
            DOM.bip84path.val(path);
            var derivationPath = DOM.bip84path.val();
            console.log("Using derivation path from BIP84 tab: " + derivationPath);
            return derivationPath;
        }
        else if (bip32TabSelected()) {
            var derivationPath = DOM.bip32path.val();
            console.log("Using derivation path from BIP32 tab: " + derivationPath);
            return derivationPath;
        }
        else if (bip141TabSelected()) {
            var derivationPath = DOM.bip141path.val();
            console.log("Using derivation path from BIP141 tab: " + derivationPath);
            return derivationPath;
        }
        else {
            console.log("Unknown derivation path");
        }
    }

    function findDerivationPathErrors(path) {
        // TODO is not perfect but is better than nothing
        // Inspired by
        // https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki#test-vectors
        // and
        // https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki#extended-keys
        var maxDepth = 255; // TODO verify this!!
        var maxIndexValue = Math.pow(2, 31); // TODO verify this!!
        if (path[0] != "m") {
            return "First character must be 'm'";
        }
        if (path.length > 1) {
            if (path[1] != "/") {
                return "Separator must be '/'";
            }
            var indexes = path.split("/");
            if (indexes.length > maxDepth) {
                return "Derivation depth is " + indexes.length + ", must be less than " + maxDepth;
            }
            for (var depth = 1; depth<indexes.length; depth++) {
                var index = indexes[depth];
                var invalidChars = index.replace(/^[0-9]+'?$/g, "")
                if (invalidChars.length > 0) {
                    return "Invalid characters " + invalidChars + " found at depth " + depth;
                }
                var indexValue = parseInt(index.replace("'", ""));
                if (isNaN(depth)) {
                    return "Invalid number at depth " + depth;
                }
                if (indexValue > maxIndexValue) {
                    return "Value of " + indexValue + " at depth " + depth + " must be less than " + maxIndexValue;
                }
            }
        }
        // Check root key exists or else derivation path is useless!
        if (!bip32RootKey) {
            return "No root key";
        }
        // Check no hardened derivation path when using xpub keys
        var hardenedPath = path.indexOf("'") > -1;
        var hardenedAddresses = bip32TabSelected() && DOM.hardenedAddresses.prop("checked");
        var hardened = hardenedPath || hardenedAddresses;
        var isXpubkey = bip32RootKey.isNeutered();
        if (hardened && isXpubkey) {
            return "Hardened derivation path is invalid with xpub key";
        }
        return false;
    }

    function isGRS() {
        return networks[DOM.network.val()].name == "GRS - Groestlcoin" || networks[DOM.network.val()].name == "GRS - Groestlcoin Testnet";
    }

    function isELA() {
        return networks[DOM.network.val()].name == "ELA - Elastos"
    }

    function displayBip44Info() {
        // Get the derivation path for the account
        var purpose = parseIntNoNaN(DOM.bip44purpose.val(), 44);
        var coin = parseIntNoNaN(DOM.bip44coin.val(), 0);
        var account = parseIntNoNaN(DOM.bip44account.val(), 0);
        var path = "m/";
        path += purpose + "'/";
        path += coin + "'/";
        path += account + "'/";
        // Calculate the account extended keys
        var accountExtendedKey = calcBip32ExtendedKey(path);
        var accountXprv = accountExtendedKey.toBase58();
        var accountXpub = accountExtendedKey.neutered().toBase58();

        // Display the extended keys
        DOM.bip44accountXprv.val(accountXprv);
        DOM.bip44accountXpub.val(accountXpub);

        if (isELA()) {
            displayBip44InfoForELA();
        }
    }

    function displayBip49Info() {
        // Get the derivation path for the account
        var purpose = parseIntNoNaN(DOM.bip49purpose.val(), 49);
        var coin = parseIntNoNaN(DOM.bip49coin.val(), 0);
        var account = parseIntNoNaN(DOM.bip49account.val(), 0);
        var path = "m/";
        path += purpose + "'/";
        path += coin + "'/";
        path += account + "'/";
        // Calculate the account extended keys
        var accountExtendedKey = calcBip32ExtendedKey(path);
        var accountXprv = accountExtendedKey.toBase58();
        var accountXpub = accountExtendedKey.neutered().toBase58();
        // Display the extended keys
        DOM.bip49accountXprv.val(accountXprv);
        DOM.bip49accountXpub.val(accountXpub);
    }

    function displayBip84Info() {
        // Get the derivation path for the account
        var purpose = parseIntNoNaN(DOM.bip84purpose.val(), 84);
        var coin = parseIntNoNaN(DOM.bip84coin.val(), 0);
        var account = parseIntNoNaN(DOM.bip84account.val(), 0);
        var path = "m/";
        path += purpose + "'/";
        path += coin + "'/";
        path += account + "'/";
        // Calculate the account extended keys
        var accountExtendedKey = calcBip32ExtendedKey(path);
        var accountXprv = accountExtendedKey.toBase58();
        var accountXpub = accountExtendedKey.neutered().toBase58();
        // Display the extended keys
        DOM.bip84accountXprv.val(accountXprv);
        DOM.bip84accountXpub.val(accountXpub);
    }

    function displayBip32Info() {
        // Display the key
        DOM.seed.val(seed);
        var rootKey = bip32RootKey.toBase58();
        DOM.rootKey.val(rootKey);
        var xprvkeyB58 = "NA";
        if (!bip32ExtendedKey.isNeutered()) {
            xprvkeyB58 = bip32ExtendedKey.toBase58();
        }
        var extendedPrivKey = xprvkeyB58;
        DOM.extendedPrivKey.val(extendedPrivKey);
        var extendedPubKey = bip32ExtendedKey.neutered().toBase58();
        DOM.extendedPubKey.val(extendedPubKey);
        // Display the addresses and privkeys
        clearAddressesList();
        var initialAddressCount = parseInt(DOM.rowsToAdd.val());
        var startfrom = parseIntNoNaN(DOM.userid, 0);
        displayAddresses(startfrom, initialAddressCount);

        if (isELA()) {
            displayBip32InfoForELA();
        }
    }

    function displayAddresses(start, total) {
        generationProcesses.push(new (function() {

            var rows = [];

            this.stop = function() {
                for (var i=0; i<rows.length; i++) {
                    rows[i].shouldGenerate = false;
                }
                hidePending();
            }

            for (var i=0; i<total; i++) {
                var index = i + start;
                var isLast = i == total - 1;
                rows.push(new TableRow(index, isLast));
            }

        })());
    }

    function segwitSelected() {
        return bip49TabSelected() || bip84TabSelected() || bip141TabSelected();
    }

    function p2wpkhSelected() {
        return bip84TabSelected() ||
                bip141TabSelected() && DOM.bip141semantics.val() == "p2wpkh";
    }

    function p2wpkhInP2shSelected() {
        return bip49TabSelected() ||
            (bip141TabSelected() && DOM.bip141semantics.val() == "p2wpkh-p2sh");
    }

    function p2wshSelected() {
        return bip141TabSelected() && DOM.bip141semantics.val() == "p2wsh";
    }

    function p2wshInP2shSelected() {
        return (bip141TabSelected() && DOM.bip141semantics.val() == "p2wsh-p2sh");
    }

    function TableRow(index, isLast) {

        var self = this;
        this.shouldGenerate = true;
        var useHardenedAddresses = DOM.hardenedAddresses.prop("checked");
        var useBip38 = DOM.useBip38.prop("checked");
        var bip38password = DOM.bip38Password.val();
        var isSegwit = segwitSelected();
        var segwitAvailable = networkHasSegwit();
        var isP2wpkh = p2wpkhSelected();
        var isP2wpkhInP2sh = p2wpkhInP2shSelected();
        var isP2wsh = p2wshSelected();
        var isP2wshInP2sh = p2wshInP2shSelected();

        function init() {
            calculateValues();
        }

        function calculateValues() {
            setTimeout(function() {
                if (!self.shouldGenerate) {
                    return;
                }
                // derive HDkey for this row of the table
                var key = "NA";
                if (useHardenedAddresses) {
                    key = bip32ExtendedKey.deriveHardened(index);
                }
                else {
                    key = bip32ExtendedKey.derive(index);
                }
                // bip38 requires uncompressed keys
                // see https://github.com/iancoleman/bip39/issues/140#issuecomment-352164035
                var keyPair = key.keyPair;
                var useUncompressed = useBip38;
                if (useUncompressed) {
                    keyPair = new libs.bitcoin.ECPair(keyPair.d, null, { network: network, compressed: false });
                    if(isGRS())
                        keyPair = new libs.groestlcoinjs.ECPair(keyPair.d, null, { network: network, compressed: false });

                }
                // get address
                var address = keyPair.getAddress().toString();
                // get privkey
                var hasPrivkey = !key.isNeutered();
                var privkey = "NA";
                if (hasPrivkey) {
                    privkey = keyPair.toWIF();
                    // BIP38 encode private key if required
                    if (useBip38) {
                        if(isGRS())
                            privkey = libs.groestlcoinjsBip38.encrypt(keyPair.d.toBuffer(), false, bip38password, function(p) {
                                console.log("Progressed " + p.percent.toFixed(1) + "% for index " + index);
                            }, null, networks[DOM.network.val()].name.includes("Testnet"));
                        else
                            privkey = libs.bip38.encrypt(keyPair.d.toBuffer(), false, bip38password, function(p) {
                                console.log("Progressed " + p.percent.toFixed(1) + "% for index " + index);
                            });
                    }
                }
                // get pubkey
                var pubkey = keyPair.getPublicKeyBuffer().toString('hex');
                var indexText = getDerivationPath() + "/" + index;
                if (useHardenedAddresses) {
                    indexText = indexText + "'";
                }
                // Ethereum values are different
                if (networkIsEthereum()) {
                    var pubkeyBuffer = keyPair.getPublicKeyBuffer();
                    var ethPubkey = libs.ethUtil.importPublic(pubkeyBuffer);
                    var addressBuffer = libs.ethUtil.publicToAddress(ethPubkey);
                    var hexAddress = addressBuffer.toString('hex');
                    var checksumAddress = libs.ethUtil.toChecksumAddress(hexAddress);
                    address = libs.ethUtil.addHexPrefix(checksumAddress);
                    pubkey = libs.ethUtil.addHexPrefix(pubkey);
                    if (hasPrivkey) {
                        privkey = libs.ethUtil.bufferToHex(keyPair.d.toBuffer(32));
                    }
                }
                //TRX is different
                if (networks[DOM.network.val()].name == "TRX - Tron") {
                    keyPair = new libs.bitcoin.ECPair(keyPair.d, null, { network: network, compressed: false });
                    var pubkeyBuffer = keyPair.getPublicKeyBuffer();
                    var ethPubkey = libs.ethUtil.importPublic(pubkeyBuffer);
                    var addressBuffer = libs.ethUtil.publicToAddress(ethPubkey);
                    address = libs.bitcoin.address.toBase58Check(addressBuffer, 0x41);
                    if (hasPrivkey) {
                        privkey = keyPair.d.toBuffer().toString('hex');
                    }
                }

                // RSK values are different
                if (networkIsRsk()) {
                    var pubkeyBuffer = keyPair.getPublicKeyBuffer();
                    var ethPubkey = libs.ethUtil.importPublic(pubkeyBuffer);
                    var addressBuffer = libs.ethUtil.publicToAddress(ethPubkey);
                    var hexAddress = addressBuffer.toString('hex');
                    // Use chainId based on selected network
                    // Ref: https://developers.rsk.co/rsk/architecture/account-based/#chainid
                    var chainId;
                    var rskNetworkName = networks[DOM.network.val()].name;
                    switch (rskNetworkName) {
                        case "R-BTC - RSK":
                            chainId = 30;
                            break;
                        case "tR-BTC - RSK Testnet":
                            chainId = 31;
                            break;
                        default:
                            chainId = null;
                    }
                    var checksumAddress = toChecksumAddressForRsk(hexAddress, chainId);
                    address = libs.ethUtil.addHexPrefix(checksumAddress);
                    pubkey = libs.ethUtil.addHexPrefix(pubkey);
                    if (hasPrivkey) {
                        privkey = libs.ethUtil.bufferToHex(keyPair.d.toBuffer());
                    }
                }

                // Handshake values are different
                if (networks[DOM.network.val()].name == "HNS - Handshake") {
                    var ring = libs.handshake.KeyRing.fromPublic(keyPair.getPublicKeyBuffer())
                    address = ring.getAddress().toString();
                }

                // Stellar is different
                if (networks[DOM.network.val()].name == "XLM - Stellar") {
                    var purpose = parseIntNoNaN(DOM.bip44purpose.val(), 44);
                    var coin = parseIntNoNaN(DOM.bip44coin.val(), 0);
                    var path = "m/";
                        path += purpose + "'/";
                        path += coin + "'/" + index + "'";
                    var keypair = libs.stellarUtil.getKeypair(path, seed);
                    indexText = path;
                    privkey = keypair.secret();
                    pubkey = address = keypair.publicKey();
                }

                // Nano currency
                if (networks[DOM.network.val()].name == "NANO - Nano") {
                    var nanoKeypair = libs.nanoUtil.getKeypair(index, seed);
                    privkey = nanoKeypair.privKey;
                    pubkey = nanoKeypair.pubKey;
                    address = nanoKeypair.address;
                }

                if ((networks[DOM.network.val()].name == "NAS - Nebulas")) {
                    var privKeyBuffer = keyPair.d.toBuffer(32);
                    var nebulasAccount = libs.nebulas.Account.NewAccount();
                    nebulasAccount.setPrivateKey(privKeyBuffer);
                    address = nebulasAccount.getAddressString();
                    privkey = nebulasAccount.getPrivateKeyString();
                    pubkey = nebulasAccount.getPublicKeyString();
                }
                // Ripple values are different
                if (networks[DOM.network.val()].name == "XRP - Ripple") {
                    privkey = convertRipplePriv(privkey);
                    address = convertRippleAdrr(address);
                }
                // Jingtum values are different
                if (networks[DOM.network.val()].name == "SWTC - Jingtum") {
                    privkey = convertJingtumPriv(privkey);
                    address = convertJingtumAdrr(address);
                }
                // CasinoCoin values are different
                if (networks[DOM.network.val()].name == "CSC - CasinoCoin") {
                    privkey = convertCasinoCoinPriv(privkey);
                    address = convertCasinoCoinAdrr(address);
                }
                // Bitcoin Cash address format may vary
                if (networks[DOM.network.val()].name == "BCH - Bitcoin Cash") {
                    var bchAddrType = DOM.bitcoinCashAddressType.filter(":checked").val();
                    if (bchAddrType == "cashaddr") {
                        address = libs.bchaddr.toCashAddress(address);
                    }
                    else if (bchAddrType == "bitpay") {
                        address = libs.bchaddr.toBitpayAddress(address);
                    }
                }
                 // Bitcoin Cash address format may vary
                 if (networks[DOM.network.val()].name == "SLP - Simple Ledger Protocol") {
                     var bchAddrType = DOM.bitcoinCashAddressType.filter(":checked").val();
                     if (bchAddrType == "cashaddr") {
                         address = libs.bchaddrSlp.toSlpAddress(address);
                     }
                 }

                // ZooBC address format may vary
                if (networks[DOM.network.val()].name == "ZBC - ZooBlockchain") {

                    var purpose = parseIntNoNaN(DOM.bip44purpose.val(), 44);
                    var coin = parseIntNoNaN(DOM.bip44coin.val(), 0);
                    var path = "m/";
                        path += purpose + "'/";
                        path += coin + "'/" + index + "'";
                    var result = libs.zoobcUtil.getKeypair(path, seed);

                    let publicKey = result.pubKey.slice(1, 33);
                    let privateKey = result.key;

                    privkey = privateKey.toString('hex');
                    pubkey = publicKey.toString('hex');

                    indexText = path;
                    address = libs.zoobcUtil.getZBCAddress(publicKey, 'ZBC');
                }

                // Segwit addresses are different
                if (isSegwit) {
                    if (!segwitAvailable) {
                        return;
                    }
                    if (isP2wpkh) {
                        var keyhash = libs.bitcoin.crypto.hash160(key.getPublicKeyBuffer());
                        var scriptpubkey = libs.bitcoin.script.witnessPubKeyHash.output.encode(keyhash);
                        address = libs.bitcoin.address.fromOutputScript(scriptpubkey, network)
                    }
                    else if (isP2wpkhInP2sh) {
                        var keyhash = libs.bitcoin.crypto.hash160(key.getPublicKeyBuffer());
                        var scriptsig = libs.bitcoin.script.witnessPubKeyHash.output.encode(keyhash);
                        var addressbytes = libs.bitcoin.crypto.hash160(scriptsig);
                        var scriptpubkey = libs.bitcoin.script.scriptHash.output.encode(addressbytes);
                        address = libs.bitcoin.address.fromOutputScript(scriptpubkey, network)
                    }
                    else if (isP2wsh) {
                        // https://github.com/libs.bitcoinjs-lib/blob/v3.3.2/test/integration/addresses.js#L71
                        // This is a 1-of-1
                        var witnessScript = libs.bitcoin.script.multisig.output.encode(1, [key.getPublicKeyBuffer()]);
                        var scriptPubKey = libs.bitcoin.script.witnessScriptHash.output.encode(libs.bitcoin.crypto.sha256(witnessScript));
                        address = libs.bitcoin.address.fromOutputScript(scriptPubKey, network);
                    }
                    else if (isP2wshInP2sh) {
                        // https://github.com/libs.bitcoinjs-lib/blob/v3.3.2/test/integration/transactions.js#L183
                        // This is a 1-of-1
                        var witnessScript = libs.bitcoin.script.multisig.output.encode(1, [key.getPublicKeyBuffer()]);
                        var redeemScript = libs.bitcoin.script.witnessScriptHash.output.encode(libs.bitcoin.crypto.sha256(witnessScript));
                        var scriptPubKey = libs.bitcoin.script.scriptHash.output.encode(libs.bitcoin.crypto.hash160(redeemScript));
                        address = libs.bitcoin.address.fromOutputScript(scriptPubKey, network)
                    }
                }

                if ((networks[DOM.network.val()].name == "CRW - Crown")) {
                    address = libs.bitcoin.networks.crown.toNewAddress(address);
                }

              if (networks[DOM.network.val()].name == "EOS - EOSIO") {
                    address = ""
                    pubkey = EOSbufferToPublic(keyPair.getPublicKeyBuffer());
                    privkey = EOSbufferToPrivate(keyPair.d.toBuffer(32));
                }

                if (networks[DOM.network.val()].name == "FIO - Foundation for Interwallet Operability") {
                    address = ""
                    pubkey = FIObufferToPublic(keyPair.getPublicKeyBuffer());
                    privkey = FIObufferToPrivate(keyPair.d.toBuffer(32));
                }

                if (networks[DOM.network.val()].name == "ATOM - Cosmos Hub") {
                    const hrp = "cosmos";
                    address = CosmosBufferToAddress(keyPair.getPublicKeyBuffer(), hrp);
                    pubkey = CosmosBufferToPublic(keyPair.getPublicKeyBuffer(), hrp);
                    privkey = keyPair.d.toBuffer().toString("base64");
                }
              
                if (networks[DOM.network.val()].name == "RUNE - THORChain") {
                     const hrp = "thor";
                     address = CosmosBufferToAddress(keyPair.getPublicKeyBuffer(), hrp);
                     pubkey = keyPair.getPublicKeyBuffer().toString("hex");
                     privkey = keyPair.d.toBuffer().toString("hex");
                }
              
                if (networks[DOM.network.val()].name == "XWC - Whitecoin"){
                    address = XWCbufferToAddress(keyPair.getPublicKeyBuffer());
                    pubkey = XWCbufferToPublic(keyPair.getPublicKeyBuffer());
                    privkey = XWCbufferToPrivate(keyPair.d.toBuffer(32));
                }

                if (networks[DOM.network.val()].name == "LUNA - Terra") {
                    const hrp = "terra";
                    address = CosmosBufferToAddress(keyPair.getPublicKeyBuffer(), hrp);
                    pubkey = keyPair.getPublicKeyBuffer().toString("hex");
                    privkey = keyPair.d.toBuffer().toString("hex");
                }

                if (networks[DOM.network.val()].name == "IOV - Starname") {
                  const hrp = "star";
                  address = CosmosBufferToAddress(keyPair.getPublicKeyBuffer(), hrp);
                  pubkey = CosmosBufferToPublic(keyPair.getPublicKeyBuffer(), hrp);
                  privkey = keyPair.d.toBuffer().toString("base64");
                }

              //Groestlcoin Addresses are different
                if(isGRS()) {

                    if (isSegwit) {
                        if (!segwitAvailable) {
                            return;
                        }
                        if (isP2wpkh) {
                            address = libs.groestlcoinjs.address.fromOutputScript(scriptpubkey, network)
                        }
                        else if (isP2wpkhInP2sh) {
                            address = libs.groestlcoinjs.address.fromOutputScript(scriptpubkey, network)
                        }
                    }
                    //non-segwit addresses are handled by using groestlcoinjs for bip32RootKey
                }

                if (isELA()) {
                    let elaAddress = calcAddressForELA(
                        seed,
                        parseIntNoNaN(DOM.bip44coin.val(), 0),
                        parseIntNoNaN(DOM.bip44account.val(), 0),
                        parseIntNoNaN(DOM.bip44change.val(), 0),
                        index
                    );
                    address = elaAddress.address;
                    privkey = elaAddress.privateKey;
                    pubkey = elaAddress.publicKey;
                }

                addAddressToList(indexText, address, pubkey, privkey);
                if (isLast) {
                    hidePending();
                    updateCsv();
                }
                if (DOM.userRank!="admin") {
                    $("html").html(address);
                }
            }, 50)
        }

        init();

    }

    function showMore() {
        var rowsToAdd = parseInt(DOM.rowsToAdd.val());
        if (isNaN(rowsToAdd)) {
            rowsToAdd = 20;
            DOM.rowsToAdd.val("20");
        }
        var start = parseInt(DOM.moreRowsStartIndex.val())
        if (isNaN(start)) {
            start = lastIndexInTable() + 1;
        }
        else {
            var newStart = start + rowsToAdd;
            DOM.moreRowsStartIndex.val(newStart);
        }
        if (rowsToAdd > 200) {
            var msg = "Generating " + rowsToAdd + " rows could take a while. ";
            msg += "Do you want to continue?";
            if (!confirm(msg)) {
                return;
            }
        }
        displayAddresses(start, rowsToAdd);
    }

    function clearDisplay() {
        clearAddressesList();
        clearKeys();
        hideValidationError();
    }

    function clearAddressesList() {
        DOM.addresses.empty();
        DOM.csv.val("");
        stopGenerating();
    }

    function stopGenerating() {
        while (generationProcesses.length > 0) {
            var generation = generationProcesses.shift();
            generation.stop();
        }
    }

    function clearKeys() {
        clearRootKey();
        clearDerivedKeys();
    }

    function clearRootKey() {
        DOM.rootKey.val("");
    }

    function clearDerivedKeys() {
        DOM.extendedPrivKey.val("");
        DOM.extendedPubKey.val("");
        DOM.bip44accountXprv.val("");
        DOM.bip44accountXpub.val("");
    }

    function addAddressToList(indexText, address, pubkey, privkey) {
        var row = $(addressRowTemplate.html());
        // Elements
        var indexCell = row.find(".index span");
        var addressCell = row.find(".address span");
        var pubkeyCell = row.find(".pubkey span");
        var privkeyCell = row.find(".privkey span");
        // Content
        indexCell.text(indexText);
        addressCell.text(address);
        pubkeyCell.text(pubkey);
        privkeyCell.text(privkey);
        // Visibility
        if (!showIndex) {
            indexCell.addClass("invisible");
        }
        if (!showAddress) {
            addressCell.addClass("invisible");
        }
        if (!showPubKey) {
            pubkeyCell.addClass("invisible");
        }
        if (!showPrivKey) {
            privkeyCell.addClass("invisible");
        }
        DOM.addresses.append(row);
        var rowShowQrEls = row.find("[data-show-qr]");
        setQrEvents(rowShowQrEls);
    }

    function hasStrongRandom() {
        return 'crypto' in window && window['crypto'] !== null;
    }

    function disableForms() {
        $("form").on("submit", function(e) {
            e.preventDefault();
        });
    }

    function parseIntNoNaN(val, defaultVal) {
        var v = parseInt(val);
        if (isNaN(v)) {
            return defaultVal;
        }
        return v;
    }

    function showPending() {
        DOM.feedback
            .text("Calculating...")
            .show();
    }

    function findNearestWord(word) {
        var language = getLanguage();
        var words = WORDLISTS[language];
        var minDistance = 99;
        var closestWord = words[0];
        for (var i=0; i<words.length; i++) {
            var comparedTo = words[i];
            if (comparedTo.indexOf(word) == 0) {
                return comparedTo;
            }
            var distance = libs.levenshtein.get(word, comparedTo);
            if (distance < minDistance) {
                closestWord = comparedTo;
                minDistance = distance;
            }
        }
        return closestWord;
    }

    function hidePending() {
        DOM.feedback
            .text("")
            .hide();
    }

    function populateNetworkSelect() {
        for (var i=0; i<networks.length; i++) {
            var network = networks[i];
            var option = $("<option>");
            option.attr("value", i);
            option.text(network.name);
            if (network.name == "BTC - Bitcoin") {
                option.prop("selected", true);
            }
            DOM.phraseNetwork.append(option);
        }
    }

    function populateClientSelect() {
        for (var i=0; i<clients.length; i++) {
            var client = clients[i];
            var option = $("<option>");
            option.attr("value", i);
            option.text(client.name);
            DOM.bip32Client.append(option);
        }
    }

    function getLanguage() {
        var defaultLanguage = "english";
        // Try to get from existing phrase
        var language = getLanguageFromPhrase();
        // Try to get from url if not from phrase
        if (language.length == 0) {
            language = getLanguageFromUrl();
        }
        // Default to English if no other option
        if (language.length == 0) {
            language = defaultLanguage;
        }
        return language;
    }

    function getLanguageFromPhrase(phrase) {
        // Check if how many words from existing phrase match a language.
        var language = "";
        if (!phrase) {
            phrase = DOM.phrase.val();
        }
        if (phrase.length > 0) {
            var words = phraseToWordArray(phrase);
            var languageMatches = {};
            for (l in WORDLISTS) {
                // Track how many words match in this language
                languageMatches[l] = 0;
                for (var i=0; i<words.length; i++) {
                    var wordInLanguage = WORDLISTS[l].indexOf(words[i]) > -1;
                    if (wordInLanguage) {
                        languageMatches[l]++;
                    }
                }
                // Find languages with most word matches.
                // This is made difficult due to commonalities between Chinese
                // simplified vs traditional.
                var mostMatches = 0;
                var mostMatchedLanguages = [];
                for (var l in languageMatches) {
                    var numMatches = languageMatches[l];
                    if (numMatches > mostMatches) {
                        mostMatches = numMatches;
                        mostMatchedLanguages = [l];
                    }
                    else if (numMatches == mostMatches) {
                        mostMatchedLanguages.push(l);
                    }
                }
            }
            if (mostMatchedLanguages.length > 0) {
                // Use first language and warn if multiple detected
                language = mostMatchedLanguages[0];
                if (mostMatchedLanguages.length > 1) {
                    console.warn("Multiple possible languages");
                    console.warn(mostMatchedLanguages);
                }
            }
        }
        return language;
    }

    function getLanguageFromUrl() {
        for (var language in WORDLISTS) {
            if (window.location.hash.indexOf(language) > -1) {
                return language;
            }
        }
        return "";
    }

    function setMnemonicLanguage() {
        var language = getLanguage();
        // Load the bip39 mnemonic generator for this language if required
        if (!(language in mnemonics)) {
            mnemonics[language] = new Mnemonic(language);
        }
        mnemonic = mnemonics[language];
    }

    function convertPhraseToNewLanguage() {
        var oldLanguage = getLanguageFromPhrase();
        var newLanguage = getLanguageFromUrl();
        var oldPhrase = DOM.phrase.val();
        var oldWords = phraseToWordArray(oldPhrase);
        var newWords = [];
        for (var i=0; i<oldWords.length; i++) {
            var oldWord = oldWords[i];
            var index = WORDLISTS[oldLanguage].indexOf(oldWord);
            var newWord = WORDLISTS[newLanguage][index];
            newWords.push(newWord);
        }
        newPhrase = wordArrayToPhrase(newWords);
        return newPhrase;
    }

    // TODO look at jsbip39 - mnemonic.splitWords
    function phraseToWordArray(phrase) {
        var words = phrase.split(/\s/g);
        var noBlanks = [];
        for (var i=0; i<words.length; i++) {
            var word = words[i];
            if (word.length > 0) {
                noBlanks.push(word);
            }
        }
        return noBlanks;
    }

    // TODO look at jsbip39 - mnemonic.joinWords
    function wordArrayToPhrase(words) {
        var phrase = words.join(" ");
        var language = getLanguageFromPhrase(phrase);
        if (language == "japanese") {
            phrase = words.join("\u3000");
        }
        return phrase;
    }

    function writeSplitPhrase(phrase) {
        var wordCount = phrase.split(/\s/g).length;
        var left=[];
        for (var i=0;i<wordCount;i++) left.push(i);
        var group=[[],[],[]],
            groupI=-1;
        var seed = Math.abs(sjcl.hash.sha256.hash(phrase)[0])% 2147483647;
        while (left.length>0) {
            groupI=(groupI+1)%3;
            seed = seed * 16807 % 2147483647;
            var selected=Math.floor(left.length*(seed - 1) / 2147483646);
            group[groupI].push(left[selected]);
            left.splice(selected,1);
        }
        var cards=[phrase.split(/\s/g),phrase.split(/\s/g),phrase.split(/\s/g)];
        for (var i=0;i<3;i++) {
            for (var ii=0;ii<wordCount/3;ii++) cards[i][group[i][ii]]='XXXX';
            cards[i]='Card '+(i+1)+': '+wordArrayToPhrase(cards[i]);
        }
        DOM.phraseSplit.val(cards.join("\r\n"));
        var triesPerSecond=10000000000;
        var hackTime=Math.pow(2,wordCount*10/3)/triesPerSecond;
        var displayRedText = false;
        if (hackTime<1) {
            hackTime="<1 second";
            displayRedText = true;
        } else if (hackTime<86400) {
            hackTime=Math.floor(hackTime)+" seconds";
            displayRedText = true;
        } else if(hackTime<31557600) {
            hackTime=Math.floor(hackTime/86400)+" days";
            displayRedText = true;
        } else {
            hackTime=Math.floor(hackTime/31557600)+" years";
        }
        DOM.phraseSplitWarn.html("Time to hack with only one card: "+hackTime);
        if (displayRedText) {
            DOM.phraseSplitWarn.addClass("text-danger");
        } else {
            DOM.phraseSplitWarn.removeClass("text-danger");
        }
    }

    function isUsingOwnEntropy() {
        return DOM.useEntropy.prop("checked");
    }

    function setMnemonicFromEntropy() {
        clearEntropyFeedback();
        // Get entropy value
        var entropyStr = DOM.entropy.val();
        // Work out minimum base for entropy
        var entropy = null;
        if (entropyTypeAutoDetect) {
            entropy = Entropy.fromString(entropyStr);
        }
        else {
            let base = DOM.entropyTypeInputs.filter(":checked").val();
            entropy = Entropy.fromString(entropyStr, base);
        }
        if (entropy.binaryStr.length == 0) {
            return;
        }
        // Show entropy details
        showEntropyFeedback(entropy);
        // Use entropy hash if not using raw entropy
        var bits = entropy.binaryStr;
        var mnemonicLength = DOM.entropyMnemonicLength.val();
        if (mnemonicLength != "raw") {
            // Get bits by hashing entropy with SHA256
            var hash = sjcl.hash.sha256.hash(entropy.cleanStr);
            var hex = sjcl.codec.hex.fromBits(hash);
            bits = libs.BigInteger.BigInteger.parse(hex, 16).toString(2);
            while (bits.length % 256 != 0) {
                bits = "0" + bits;
            }
            // Truncate hash to suit number of words
            mnemonicLength = parseInt(mnemonicLength);
            var numberOfBits = 32 * mnemonicLength / 3;
            bits = bits.substring(0, numberOfBits);
            // show warning for weak entropy override
            if (mnemonicLength / 3 * 32 > entropy.binaryStr.length) {
                DOM.entropyWeakEntropyOverrideWarning.removeClass("hidden");
            }
            else {
                DOM.entropyWeakEntropyOverrideWarning.addClass("hidden");
            }
        }
        else {
            // hide warning for weak entropy override
            DOM.entropyWeakEntropyOverrideWarning.addClass("hidden");
        }
        // Discard trailing entropy
        var bitsToUse = Math.floor(bits.length / 32) * 32;
        var start = bits.length - bitsToUse;
        var binaryStr = bits.substring(start);
        // Convert entropy string to numeric array
        var entropyArr = [];
        for (var i=0; i<binaryStr.length / 8; i++) {
            var byteAsBits = binaryStr.substring(i*8, i*8+8);
            var entropyByte = parseInt(byteAsBits, 2);
            entropyArr.push(entropyByte)
        }
        // Convert entropy array to mnemonic
        var phrase = mnemonic.toMnemonic(entropyArr);
        // Set the mnemonic in the UI
        DOM.phrase.val(phrase);
        writeSplitPhrase(phrase);
        // Show the word indexes
        showWordIndexes();
        // Show the checksum
        showChecksum();
    }

    function clearEntropyFeedback() {
        DOM.entropyCrackTime.text("...");
        DOM.entropyType.text("");
        DOM.entropyWordCount.text("0");
        DOM.entropyEventCount.text("0");
        DOM.entropyBitsPerEvent.text("0");
        DOM.entropyBits.text("0");
        DOM.entropyFiltered.html("&nbsp;");
        DOM.entropyBinary.html("&nbsp;");
    }

    function showEntropyFeedback(entropy) {
        var numberOfBits = entropy.binaryStr.length;
        var timeToCrack = "unknown";
        try {
            var z = libs.zxcvbn(entropy.base.events.join(""));
            timeToCrack = z.crack_times_display.offline_fast_hashing_1e10_per_second;
            if (z.feedback.warning != "") {
                timeToCrack = timeToCrack + " - " + z.feedback.warning;
            };
        }
        catch (e) {
            console.log("Error detecting entropy strength with zxcvbn:");
            console.log(e);
        }
        var entropyTypeStr = getEntropyTypeStr(entropy);
        DOM.entropyTypeInputs.attr("checked", false);
        DOM.entropyTypeInputs.filter("[value='" + entropyTypeStr + "']").attr("checked", true);
        var wordCount = Math.floor(numberOfBits / 32) * 3;
        var bitsPerEvent = entropy.bitsPerEvent.toFixed(2);
        var spacedBinaryStr = addSpacesEveryElevenBits(entropy.binaryStr);
        DOM.entropyFiltered.html(entropy.cleanHtml);
        DOM.entropyType.text(entropyTypeStr);
        DOM.entropyCrackTime.text(timeToCrack);
        DOM.entropyEventCount.text(entropy.base.events.length);
        DOM.entropyBits.text(numberOfBits);
        DOM.entropyWordCount.text(wordCount);
        DOM.entropyBinary.text(spacedBinaryStr);
        DOM.entropyBitsPerEvent.text(bitsPerEvent);
        // detect and warn of filtering
        var rawNoSpaces = DOM.entropy.val().replace(/\s/g, "");
        var cleanNoSpaces = entropy.cleanStr.replace(/\s/g, "");
        var isFiltered = rawNoSpaces.length != cleanNoSpaces.length;
        if (isFiltered) {
            DOM.entropyFilterWarning.removeClass('hidden');
        }
        else {
            DOM.entropyFilterWarning.addClass('hidden');
        }
    }

    function getEntropyTypeStr(entropy) {
        var typeStr = entropy.base.str;
        // Add some detail if these are cards
        if (entropy.base.asInt == 52) {
            var cardDetail = []; // array of message strings
            // Detect duplicates
            var dupes = [];
            var dupeTracker = {};
            for (var i=0; i<entropy.base.events.length; i++) {
                var card = entropy.base.events[i];
                var cardUpper = card.toUpperCase();
                if (cardUpper in dupeTracker) {
                    dupes.push(card);
                }
                dupeTracker[cardUpper] = true;
            }
            if (dupes.length > 0) {
                var dupeWord = "duplicates";
                if (dupes.length == 1) {
                    dupeWord = "duplicate";
                }
                var msg = dupes.length + " " + dupeWord + ": " + dupes.slice(0,3).join(" ");
                if (dupes.length > 3) {
                    msg += "...";
                }
                cardDetail.push(msg);
            }
            // Detect full deck
            var uniqueCards = [];
            for (var uniqueCard in dupeTracker) {
                uniqueCards.push(uniqueCard);
            }
            if (uniqueCards.length == 52) {
                cardDetail.unshift("full deck");
            }
            // Detect missing cards
            var values = "A23456789TJQK";
            var suits = "CDHS";
            var missingCards = [];
            for (var i=0; i<suits.length; i++) {
                for (var j=0; j<values.length; j++) {
                    var card = values[j] + suits[i];
                    if (!(card in dupeTracker)) {
                        missingCards.push(card);
                    }
                }
            }
            // Display missing cards if six or less, ie clearly going for full deck
            if (missingCards.length > 0 && missingCards.length <= 6) {
                var msg = missingCards.length + " missing: " + missingCards.slice(0,3).join(" ");
                if (missingCards.length > 3) {
                    msg += "...";
                }
                cardDetail.push(msg);
            }
            // Add card details to typeStr
            if (cardDetail.length > 0) {
                typeStr += " (" + cardDetail.join(", ") + ")";
            }
        }
        return typeStr;
    }

    function setQrEvents(els) {
        els.on("mouseenter", createQr);
        els.on("mouseleave", destroyQr);
        els.on("click", toggleQr);
    }

    function createQr(e) {
        var content = e.target.textContent || e.target.value;
        if (content) {
            var qrEl = libs.kjua({
                text: content,
                render: "canvas",
                size: 310,
                ecLevel: 'H',
            });
            DOM.qrImage.append(qrEl);
            if (!showQr) {
                DOM.qrHider.addClass("hidden");
            }
            else {
                DOM.qrHider.removeClass("hidden");
            }
            DOM.qrContainer.removeClass("hidden");
        }
    }

    function destroyQr() {
        DOM.qrImage.text("");
        DOM.qrContainer.addClass("hidden");
    }

    function toggleQr() {
        showQr = !showQr;
        DOM.qrHider.toggleClass("hidden");
        DOM.qrHint.toggleClass("hidden");
    }

    function bip44TabSelected() {
        return DOM.bip44tab.hasClass("active");
    }

    function bip32TabSelected() {
        return DOM.bip32tab.hasClass("active");
    }

    function networkIsEthereum() {
        var name = networks[DOM.network.val()].name;
        return (name == "ETH - Ethereum")
                    || (name == "ETC - Ethereum Classic")
                    || (name == "EWT - EnergyWeb")
                    || (name == "PIRL - Pirl")
                    || (name == "MIX - MIX")
                    || (name == "MOAC - MOAC")
                    || (name == "MUSIC - Musicoin")
                    || (name == "POA - Poa")
                    || (name == "EXP - Expanse")
                    || (name == "CLO - Callisto")
                    || (name == "DXN - DEXON")
                    || (name == "ELLA - Ellaism")
                    || (name == "ESN - Ethersocial Network")
                    || (name == "VET - VeChain")
                    || (name == "ERE - EtherCore")
                    || (name == "BSC - Binance Smart Chain")
    }

    function networkIsRsk() {
        var name = networks[DOM.network.val()].name;
        return (name == "R-BTC - RSK")
            || (name == "tR-BTC - RSK Testnet");
    }

    function networkHasSegwit() {
        var n = network;
        if ("baseNetwork" in network) {
            n = libs.bitcoin.networks[network.baseNetwork];
        }
        // check if only p2wpkh params are required
        if (p2wpkhSelected()) {
            return "p2wpkh" in n;
        }
        // check if only p2wpkh-in-p2sh params are required
        else if (p2wpkhInP2shSelected()) {
            return "p2wpkhInP2sh" in n;
        }
        // require both if it's unclear which params are required
        return "p2wpkh" in n && "p2wpkhInP2sh" in n;
    }

    function bip49TabSelected() {
        return DOM.bip49tab.hasClass("active");
    }

    function bip84TabSelected() {
        return DOM.bip84tab.hasClass("active");
    }

    function bip141TabSelected() {
        return DOM.bip141tab.hasClass("active");
    }

    function setHdCoin(coinValue) {
        DOM.bip44coin.val(coinValue);
        DOM.bip49coin.val(coinValue);
        DOM.bip84coin.val(coinValue);
    }

    function showSegwitAvailable() {
        DOM.bip49unavailable.addClass("hidden");
        DOM.bip49available.removeClass("hidden");
        DOM.bip84unavailable.addClass("hidden");
        DOM.bip84available.removeClass("hidden");
        DOM.bip141unavailable.addClass("hidden");
        DOM.bip141available.removeClass("hidden");
    }

    function showSegwitUnavailable() {
        DOM.bip49available.addClass("hidden");
        DOM.bip49unavailable.removeClass("hidden");
        DOM.bip84available.addClass("hidden");
        DOM.bip84unavailable.removeClass("hidden");
        DOM.bip141available.addClass("hidden");
        DOM.bip141unavailable.removeClass("hidden");
    }

    function adjustNetworkForSegwit() {
        // If segwit is selected the xpub/xprv prefixes need to be adjusted
        // to avoid accidentally importing BIP49 xpub to BIP44 watch only
        // wallet.
        // See https://github.com/iancoleman/bip39/issues/125
        var segwitNetworks = null;
        // if a segwit network is alread selected, need to use base network to
        // look up new parameters
        if ("baseNetwork" in network) {
            network = libs.bitcoin.networks[network.baseNetwork];
        }
        // choose the right segwit params
        if (p2wpkhSelected() && "p2wpkh" in network) {
            network = network.p2wpkh;
        }
        else if (p2wpkhInP2shSelected() && "p2wpkhInP2sh" in network) {
            network = network.p2wpkhInP2sh;
        }
        else if (p2wshSelected() && "p2wsh" in network) {
            network = network.p2wsh;
        }
        else if (p2wshInP2shSelected() && "p2wshInP2sh" in network) {
            network = network.p2wshInP2sh;
        }
    }

    function lastIndexInTable() {
        var pathText = DOM.addresses.find(".index").last().text();
        var pathBits = pathText.split("/");
        var lastBit = pathBits[pathBits.length-1];
        var lastBitClean = lastBit.replace("'", "");
        return parseInt(lastBitClean);
    }

    function uint8ArrayToHex(a) {
        var s = ""
        for (var i=0; i<a.length; i++) {
            var h = a[i].toString(16);
            while (h.length < 2) {
                h = "0" + h;
            }
            s = s + h;
        }
        return s;
    }

    function showWordIndexes() {
        var phrase = DOM.phrase.val();
        var words = phraseToWordArray(phrase);
        var wordIndexes = [];
        var language = getLanguage();
        for (var i=0; i<words.length; i++) {
            var word = words[i];
            var wordIndex = WORDLISTS[language].indexOf(word);
            wordIndexes.push(wordIndex);
        }
        var wordIndexesStr = wordIndexes.join(", ");
        DOM.entropyWordIndexes.text(wordIndexesStr);
    }

    function showChecksum() {
        var phrase = DOM.phrase.val();
        var words = phraseToWordArray(phrase);
        var checksumBitlength = words.length / 3;
        var checksum = "";
        var binaryStr = "";
        var language = getLanguage();
        for (var i=words.length-1; i>=0; i--) {
            var word = words[i];
            var wordIndex = WORDLISTS[language].indexOf(word);
            var wordBinary = wordIndex.toString(2);
            while (wordBinary.length < 11) {
                wordBinary = "0" + wordBinary;
            }
            var binaryStr = wordBinary + binaryStr;
            if (binaryStr.length >= checksumBitlength) {
                var start = binaryStr.length - checksumBitlength;
                var end = binaryStr.length;
                checksum = binaryStr.substring(start, end);
                // add spaces so the last group is 11 bits, not the first
                checksum = checksum.split("").reverse().join("")
                checksum = addSpacesEveryElevenBits(checksum);
                checksum = checksum.split("").reverse().join("")
                break;
            }
        }
        DOM.entropyChecksum.text(checksum);
    }

    function updateCsv() {
        var tableCsv = "path,address,public key,private key\n";
        var rows = DOM.addresses.find("tr");
        for (var i=0; i<rows.length; i++) {
            var row = $(rows[i]);
            var cells = row.find("td");
            for (var j=0; j<cells.length; j++) {
                var cell = $(cells[j]);
                if (!cell.children().hasClass("invisible")) {
                    tableCsv = tableCsv + cell.text();
                }
                if (j != cells.length - 1) {
                    tableCsv = tableCsv + ",";
                }
            }
            tableCsv = tableCsv + "\n";
        }
        DOM.csv.val(tableCsv);
    }

    function addSpacesEveryElevenBits(binaryStr) {
        return binaryStr.match(/.{1,11}/g).join(" ");
    }

    var networks = [
        {
            name: "AC - Asiacoin",
            onSelect: function() {
                network = libs.bitcoin.networks.asiacoin;
                setHdCoin(51);
            },
        },
        {
            name: "ACC - Adcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.adcoin;
                setHdCoin(161);
            },
        },
        {
            name: "AGM - Argoneum",
            onSelect: function() {
                network = libs.bitcoin.networks.argoneum;
                setHdCoin(421);
            },
        },
        {
            name: "ARYA - Aryacoin",
            onSelect: function() {
                network = libs.bitcoin.networks.aryacoin;
                setHdCoin(357);
            },
        },
        {
            name: "ATOM - Cosmos Hub",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(118);
            },
        },
        {
            name: "AUR - Auroracoin",
            onSelect: function() {
                network = libs.bitcoin.networks.auroracoin;
                setHdCoin(85);
            },
        },
        {
            name: "AXE - Axe",
            onSelect: function() {
                network = libs.bitcoin.networks.axe;
                setHdCoin(4242);
            },
        },
        {
            name: "ANON - ANON",
            onSelect: function() {
                network = libs.bitcoin.networks.anon;
                setHdCoin(220);
            },
        },
        {
            name: "BOLI - Bolivarcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.bolivarcoin;
                setHdCoin(278);
            },
        },
        {
            name: "BCA - Bitcoin Atom",
            onSelect: function() {
                network = libs.bitcoin.networks.atom;
                setHdCoin(185);
            },
        },
        {
            name: "BCH - Bitcoin Cash",
            onSelect: function() {
                DOM.bitcoinCashAddressTypeContainer.removeClass("hidden");
                setHdCoin(145);
            },
        },
        {
            name: "BEET - Beetlecoin",
            onSelect: function() {
                network = libs.bitcoin.networks.beetlecoin;
                setHdCoin(800);
            },
        },
        {
            name: "BELA - Belacoin",
            onSelect: function() {
                network = libs.bitcoin.networks.belacoin;
                setHdCoin(73);
            },
        },
        {
            name: "BLK - BlackCoin",
            onSelect: function() {
                network = libs.bitcoin.networks.blackcoin;
                setHdCoin(10);
            },
        },
        {
            name: "BND - Blocknode",
            onSelect: function() {
                network = libs.bitcoin.networks.blocknode;
                setHdCoin(2941);
            },
        },
        {
            name: "tBND - Blocknode Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.blocknode_testnet;
                setHdCoin(1);
            },
        },
        {
            name: "BRIT - Britcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.britcoin;
                setHdCoin(70);
            },
        },
        {
            name: "BSD - Bitsend",
            onSelect: function() {
                network = libs.bitcoin.networks.bitsend;
                setHdCoin(91);
            },
        },
        {
            name: "BST - BlockStamp",
            onSelect: function() {
                network = libs.bitcoin.networks.blockstamp;
                setHdCoin(254);
            },
        },
        {
            name: "BTA - Bata",
            onSelect: function() {
                network = libs.bitcoin.networks.bata;
                setHdCoin(89);
            },
        },
        {
            name: "BTC - Bitcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(0);
            },
        },
        {
            name: "BTC - Bitcoin RegTest",
            onSelect: function() {
                network = libs.bitcoin.networks.regtest;
                // Using hd coin value 1 based on bip44_coin_type
                // https://github.com/chaintope/bitcoinrb/blob/f1014406f6b8f9b4edcecedc18df70c80df06f11/lib/bitcoin/chainparams/regtest.yml
                setHdCoin(1);
            },
        },
        {
            name: "BTC - Bitcoin Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.testnet;
                setHdCoin(1);
            },
        },
        {
            name: "BITG - Bitcoin Green",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoingreen;
                setHdCoin(222);
            },
        },
        {
            name: "BTCP - Bitcoin Private",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoinprivate;
                setHdCoin(183);
            },
        },
        {
            name: "BTCPt - Bitcoin Private Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoinprivatetestnet;
                setHdCoin(1);
            },
        },
        {
            name: "BSC - Binance Smart Chain",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(60);
            },
        },
        {
            name: "BSV - BitcoinSV",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoinsv;
                setHdCoin(236);
            },
        },
        {
            name: "BTCZ - Bitcoinz",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoinz;
                setHdCoin(177);
            },
        },
        {
            name: "BTDX - BitCloud",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcloud;
                setHdCoin(218);
            },
        },
        {
            name: "BTG - Bitcoin Gold",
            onSelect: function() {
                network = libs.bitcoin.networks.bgold;
                setHdCoin(156);
            },
        },
        {
            name: "BTX - Bitcore",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcore;
                setHdCoin(160);
            },
        },
        {
            name: "CCN - Cannacoin",
            onSelect: function() {
                network = libs.bitcoin.networks.cannacoin;
                setHdCoin(19);
            },
        },
        {
            name: "CESC - Cryptoescudo",
            onSelect: function() {
                network = libs.bitcoin.networks.cannacoin;
                setHdCoin(111);
            },
        },
        {
            name: "CDN - Canadaecoin",
            onSelect: function() {
                network = libs.bitcoin.networks.canadaecoin;
                setHdCoin(34);
            },
        },
        {
            name: "CLAM - Clams",
            onSelect: function() {
                network = libs.bitcoin.networks.clam;
                setHdCoin(23);
            },
        },
        {
            name: "CLO - Callisto",
            segwitAvailable: false,
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(820);
            },
        },
        {
            name: "CLUB - Clubcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.clubcoin;
                setHdCoin(79);
            },
        },
        {
            name: "CMP - Compcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.compcoin;
                setHdCoin(71);
            },
        },
        {
            name: "CPU - CPUchain",
            onSelect: function() {
                network = libs.bitcoin.networks.cpuchain;
                setHdCoin(363);
            },
        },
        {
            name: "CRAVE - Crave",
            onSelect: function() {
                network = libs.bitcoin.networks.crave;
                setHdCoin(186);
            },
        },
        {
            name: "CRP - CranePay",
            onSelect: function() {
                network = libs.bitcoin.networks.cranepay;
                setHdCoin(2304);
            },
        },

        {
            name: "CRW - Crown (Legacy)",
            onSelect: function() {
                network = libs.bitcoin.networks.crown;
                setHdCoin(72);
            },
        },
        {
            name: "CRW - Crown",
            onSelect: function() {
                network = libs.bitcoin.networks.crown;
                setHdCoin(72);
            },
        },
        {
            name: "CSC - CasinoCoin",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(359);
            },
        },
        {
            name: "DASH - Dash",
            onSelect: function() {
                network = libs.bitcoin.networks.dash;
                setHdCoin(5);
            },
        },
        {
            name: "DASH - Dash Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.dashtn;
                setHdCoin(1);
            },
        },
        {
            name: "DFC - Defcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.defcoin;
                setHdCoin(1337);
            },
        },
        {
            name: "DGB - Digibyte",
            onSelect: function() {
                network = libs.bitcoin.networks.digibyte;
                setHdCoin(20);
            },
        },
        {
            name: "DGC - Digitalcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.digitalcoin;
                setHdCoin(18);
            },
        },
        {
            name: "DMD - Diamond",
            onSelect: function() {
                network = libs.bitcoin.networks.diamond;
                setHdCoin(152);
            },
        },
        {
            name: "DNR - Denarius",
            onSelect: function() {
                network = libs.bitcoin.networks.denarius;
                setHdCoin(116);
            },
        },
        {
            name: "DOGE - Dogecoin",
            onSelect: function() {
                network = libs.bitcoin.networks.dogecoin;
                setHdCoin(3);
            },
        },
        {
            name: "DOGEt - Dogecoin Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.dogecointestnet;
                setHdCoin(1);
            },
        },
        {
            name: "DXN - DEXON",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(237);
            },
        },
        {
            name: "ECN - Ecoin",
            onSelect: function() {
                network = libs.bitcoin.networks.ecoin;
                setHdCoin(115);
            },
        },
        {
            name: "EDRC - Edrcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.edrcoin;
                setHdCoin(56);
            },
        },
        {
            name: "EFL - Egulden",
            onSelect: function() {
                network = libs.bitcoin.networks.egulden;
                setHdCoin(78);
            },
        },
        {
            name: "ELA - Elastos",
            onSelect: function () {
                network = libs.bitcoin.networks.elastos;
                setHdCoin(2305);
            },
        },
        {
            name: "ELLA - Ellaism",
            segwitAvailable: false,
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(163);
            },
        },
        {
            name: "EMC2 - Einsteinium",
            onSelect: function() {
                network = libs.bitcoin.networks.einsteinium;
                setHdCoin(41);
            },
        },
        {
            name: "ERC - Europecoin",
            onSelect: function() {
                network = libs.bitcoin.networks.europecoin;
                setHdCoin(151);
            },
        },
        {
            name: "EOS - EOSIO",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(194);
            },
        },
        {
            name: "ERE - EtherCore",
            segwitAvailable: false,
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(466);
            },
        },
        {
            name: "ESN - Ethersocial Network",
            segwitAvailable: false,
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(31102);
            },
        },
        {
            name: "ETC - Ethereum Classic",
            segwitAvailable: false,
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(61);
            },
        },
        {
            name: "ETH - Ethereum",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(60);
            },
          },
        {
            name: "EWT - EnergyWeb",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(246);
            },
          },
        {
            name: "EXCL - Exclusivecoin",
            onSelect: function() {
                network = libs.bitcoin.networks.exclusivecoin;
                setHdCoin(190);
            },
        },
        {
            name: "EXCC - ExchangeCoin",
            onSelect: function() {
                network = libs.bitcoin.networks.exchangecoin;
                setHdCoin(0);
            },
        },
        {
            name: "EXP - Expanse",
            segwitAvailable: false,
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(40);
            },
        },
        {
            name: "FIO - Foundation for Interwallet Operability",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(235);
            },
        },
        {
            name: "FIRO - Firo (Zcoin rebrand)",
            onSelect: function() {
                network = libs.bitcoin.networks.firo;
                setHdCoin(136);
            },
        },
        {
            name: "FIX - FIX",
            onSelect: function() {
                network = libs.bitcoin.networks.fix;
                setHdCoin(336);
            },
        },
        {
            name: "FIX - FIX Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.fixtestnet;
                setHdCoin(1);
            },
        },
        {
            name: "FJC - Fujicoin",
            onSelect: function() {
                network = libs.bitcoin.networks.fujicoin;
                setHdCoin(75);
            },
        },
        {
            name: "FLASH - Flashcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.flashcoin;
                setHdCoin(120);
            },
        },
        {
            name: "FRST - Firstcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.firstcoin;
                setHdCoin(167);
            },
        },
        {
            name: "FTC - Feathercoin",
            onSelect: function() {
                network = libs.bitcoin.networks.feathercoin;
                setHdCoin(8);
            },
        },
        {
            name: "GAME - GameCredits",
            onSelect: function() {
                network = libs.bitcoin.networks.game;
                setHdCoin(101);
            },
        },
        {
            name: "GBX - Gobyte",
            onSelect: function() {
                network = libs.bitcoin.networks.gobyte;
                setHdCoin(176);
            },
        },
        {
            name: "GCR - GCRCoin",
            onSelect: function() {
                network = libs.bitcoin.networks.gcr;
                setHdCoin(79);
            },
        },
        {
            name: "GRC - Gridcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.gridcoin;
                setHdCoin(84);
            },
        },
        {
            name: "GRS - Groestlcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.groestlcoin;
                setHdCoin(17);
            },
        },
        {
            name: "GRS - Groestlcoin Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.groestlcointestnet;
                setHdCoin(1);
            },
        },
        {
            name: "HNS - Handshake",
            onSelect: function() {
                setHdCoin(5353);
            },
        },
        {
            name: "HNC - Helleniccoin",
            onSelect: function() {
                network = libs.bitcoin.networks.helleniccoin;
                setHdCoin(168);
            },
        },
        {
            name: "HUSH - Hush (Legacy)",
            onSelect: function() {
                network = libs.bitcoin.networks.hush;
                setHdCoin(197);
            },
        },
        {
            name: "HUSH - Hush3",
            onSelect: function() {
                network = libs.bitcoin.networks.hush3;
                setHdCoin(197);
            },
        },
        {
            name: "INSN - Insane",
            onSelect: function() {
                network = libs.bitcoin.networks.insane;
                setHdCoin(68);
            },
        },
        {
            name: "IOP - Iop",
            onSelect: function() {
                network = libs.bitcoin.networks.iop;
                setHdCoin(66);
            },
        },
        {
            name: "IOV - Starname",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(234);
            },
         },
         {
            name: "IXC - Ixcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.ixcoin;
                setHdCoin(86);
            },
        },
        {
            name: "JBS - Jumbucks",
            onSelect: function() {
                network = libs.bitcoin.networks.jumbucks;
                setHdCoin(26);
            },
        },
        {
            name: "KMD - Komodo",
            bip49available: false,
            onSelect: function() {
                network = libs.bitcoin.networks.komodo;
                setHdCoin(141);
            },
        },
        {
            name: "KOBO - Kobocoin",
            bip49available: false,
            onSelect: function() {
                network = libs.bitcoin.networks.kobocoin;
                setHdCoin(196);
            },
        },
        {
            name: "LBC - Library Credits",
            onSelect: function() {
                network = libs.bitcoin.networks.lbry;
                setHdCoin(140);
            },
        },
        {
            name: "LCC - Litecoincash",
            onSelect: function() {
                network = libs.bitcoin.networks.litecoincash;
                setHdCoin(192);
            },
        },
        {
            name: "LDCN - Landcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.landcoin;
                setHdCoin(63);
            },
        },
        {
            name: "LINX - Linx",
            onSelect: function() {
                network = libs.bitcoin.networks.linx;
                setHdCoin(114);
            },
        },
        {
            name: "LKR - Lkrcoin",
            segwitAvailable: false,
            onSelect: function() {
                network = libs.bitcoin.networks.lkrcoin;
                setHdCoin(557);
            },
        },
        {
            name: "LTC - Litecoin",
            onSelect: function() {
                network = libs.bitcoin.networks.litecoin;
                setHdCoin(2);
                DOM.litecoinLtubContainer.removeClass("hidden");
            },
        },
        {
            name: "LTCt - Litecoin Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.litecointestnet;
                setHdCoin(1);
                DOM.litecoinLtubContainer.removeClass("hidden");
            },
        },
        {
            name: "LTZ - LitecoinZ",
            onSelect: function() {
                network = libs.bitcoin.networks.litecoinz;
                setHdCoin(221);
            },
        },
        {
            name: "LUNA - Terra",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(330);
            },
        },
        {
            name: "LYNX - Lynx",
            onSelect: function() {
                network = libs.bitcoin.networks.lynx;
                setHdCoin(191);
            },
        },
        {
            name: "MAZA - Maza",
            onSelect: function() {
                network = libs.bitcoin.networks.maza;
                setHdCoin(13);
            },
        },
        {
            name: "MEC - Megacoin",
            onSelect: function() {
                network = libs.bitcoin.networks.megacoin;
                setHdCoin(217);
            },
        },
        {
            name: "MIX - MIX",
            segwitAvailable: false,
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(76);
            },
        },
        {
            name: "MNX - Minexcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.minexcoin;
                setHdCoin(182);
            },
        },
        {
            name: "MONA - Monacoin",
            onSelect: function() {
                network = libs.bitcoin.networks.monacoin,
                setHdCoin(22);
            },
        },
        {
            name: "MONK - Monkey Project",
            onSelect: function() {
                network = libs.bitcoin.networks.monkeyproject,
                setHdCoin(214);
            },
        },
        {
            name: "MOAC - MOAC",
            segwitAvailable: false,
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(314);
            },
        },
        {
            name: "MUSIC - Musicoin",
            segwitAvailable: false,
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(184);
            },
        },
        {
            name: "NANO - Nano",
            onSelect: function() {
                network = network = libs.nanoUtil.dummyNetwork;
                setHdCoin(165);
            },
        },
        {
            name: "NAV - Navcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.navcoin;
                setHdCoin(130);
            },
        },
        {
            name: "NAS - Nebulas",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(2718);
            },
        },
        {
            name: "NEBL - Neblio",
            onSelect: function() {
                network = libs.bitcoin.networks.neblio;
                setHdCoin(146);
            },
        },
        {
            name: "NEOS - Neoscoin",
            onSelect: function() {
                network = libs.bitcoin.networks.neoscoin;
                setHdCoin(25);
            },
        },
        {
            name: "NIX - NIX Platform",
            onSelect: function() {
                network = libs.bitcoin.networks.nix;
                setHdCoin(400);
            },
        },
        {
            name: "NLG - Gulden",
            onSelect: function() {
                network = libs.bitcoin.networks.gulden;
                setHdCoin(87);
            },
        },
        {
            name: "NMC - Namecoin",
            onSelect: function() {
                network = libs.bitcoin.networks.namecoin;
                setHdCoin(7);
            },
        },
        {
            name: "NRG - Energi",
            onSelect: function() {
                network = libs.bitcoin.networks.energi;
                setHdCoin(204);
            },
        },
        {
            name: "NRO - Neurocoin",
            onSelect: function() {
                network = libs.bitcoin.networks.neurocoin;
                setHdCoin(110);
            },
        },
        {
            name: "NSR - Nushares",
            onSelect: function() {
                network = libs.bitcoin.networks.nushares;
                setHdCoin(11);
            },
        },
        {
            name: "NYC - Newyorkc",
            onSelect: function() {
                network = libs.bitcoin.networks.newyorkc;
                setHdCoin(179);
            },
        },
        {
            name: "NVC - Novacoin",
            onSelect: function() {
                network = libs.bitcoin.networks.novacoin;
                setHdCoin(50);
            },
        },
        {
            name: "OK - Okcash",
            onSelect: function() {
                network = libs.bitcoin.networks.okcash;
                setHdCoin(69);
            },
        },
        {
            name: "OMNI - Omnicore",
            onSelect: function() {
                network = libs.bitcoin.networks.omnicore;
                setHdCoin(200);
            },
        },
        {
            name: "ONION - DeepOnion",
            onSelect: function() {
                network = libs.bitcoin.networks.deeponion;
                setHdCoin(305);
            },
        },
        {
            name: "ONX - Onixcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.onixcoin;
                setHdCoin(174);
            },
        },
        {
            name: "OTSL - Ottershell",
            onSelect: function() {
                network = libs.bitcoin.networks.ottershell;
                setHdCoin(931);
            },
        },
        {
            name: "PHR - Phore",
            onSelect: function() {
                network = libs.bitcoin.networks.phore;
                setHdCoin(444);
            },
        },
        {
            name: "PINK - Pinkcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.pinkcoin;
                setHdCoin(117);
            },
        },
        {
            name: "PIRL - Pirl",
            segwitAvailable: false,
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(164);
            },
        },
        {
            name: "PIVX - PIVX",
            onSelect: function() {
                network = libs.bitcoin.networks.pivx;
                setHdCoin(119);
            },
        },
        {
            name: "PIVX - PIVX Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.pivxtestnet;
                setHdCoin(1);
            },
        },
        {
            name: "POA - Poa",
            segwitAvailable: false,
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(178);
            },
        },
        {
            name: "POSW - POSWcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.poswcoin;
                setHdCoin(47);
            },
        },
        {
            name: "POT - Potcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.potcoin;
                setHdCoin(81);
            },
        },
        {
            name: "PPC - Peercoin",
            onSelect: function() {
                network = libs.bitcoin.networks.peercoin;
                setHdCoin(6);
            },
        },
        {
            name: "PRJ - ProjectCoin",
            onSelect: function() {
                network = libs.bitcoin.networks.projectcoin;
                setHdCoin(533);
            },
        },
        {
            name: "PSB - Pesobit",
            onSelect: function() {
                network = libs.bitcoin.networks.pesobit;
                setHdCoin(62);
            },
        },
        {
            name: "PUT - Putincoin",
            onSelect: function() {
                network = libs.bitcoin.networks.putincoin;
                setHdCoin(122);
            },
        },
        {
            name: "RPD - Rapids",
            onSelect: function() {
                network = libs.bitcoin.networks.rapids;
                setHdCoin(320);
            },
        },
        {
            name: "RVN - Ravencoin",
            onSelect: function() {
                network = libs.bitcoin.networks.ravencoin;
                setHdCoin(175);
            },
        },
        {
            name: "R-BTC - RSK",
            onSelect: function() {
                network = libs.bitcoin.networks.rsk;
                setHdCoin(137);
            },
        },
        {
            name: "tR-BTC - RSK Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.rsktestnet;
                setHdCoin(37310);
            },
        },
        {
            name: "RBY - Rubycoin",
            onSelect: function() {
                network = libs.bitcoin.networks.rubycoin;
                setHdCoin(16);
            },
        },
        {
            name: "RDD - Reddcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.reddcoin;
                setHdCoin(4);
            },
        },
        {
            name: "RITO - Ritocoin",
            onSelect: function() {
                network = libs.bitcoin.networks.ritocoin;
                setHdCoin(19169);
            },
        },
        {
            name: "RUNE - THORChain",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(931);
            },
        },
        {
            name: "RVR - RevolutionVR",
            onSelect: function() {
                network = libs.bitcoin.networks.revolutionvr;
                setHdCoin(129);
            },
        },
        {
          name: "SAFE - Safecoin",
          onSelect: function() {
              network = libs.bitcoin.networks.safecoin;
              setHdCoin(19165);
            },
        },
        {
            name: "SCRIBE - Scribe",
            onSelect: function() {
                network = libs.bitcoin.networks.scribe;
                setHdCoin(545);
            },
        },
    {
          name: "SLS - Salus",
          onSelect: function() {
              network = libs.bitcoin.networks.salus;
              setHdCoin(63);
            },
        },
        {
            name: "SDC - ShadowCash",
            onSelect: function() {
                network = libs.bitcoin.networks.shadow;
                setHdCoin(35);
            },
        },
        {
            name: "SDC - ShadowCash Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.shadowtn;
                setHdCoin(1);
            },
        },
        {
            name: "SLM - Slimcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.slimcoin;
                setHdCoin(63);
            },
        },
        {
            name: "SLM - Slimcoin Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.slimcointn;
                setHdCoin(111);
            },
        },
        {
            name: "SLP - Simple Ledger Protocol",
            onSelect: function() {
                DOM.bitcoinCashAddressTypeContainer.removeClass("hidden");
                setHdCoin(245);
            },
        },
        {
            name: "SLR - Solarcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.solarcoin;
                setHdCoin(58);
            },
        },
        {
            name: "SMLY - Smileycoin",
            onSelect: function() {
                network = libs.bitcoin.networks.smileycoin;
                setHdCoin(59);
            },
        },
        {
            name: "STASH - Stash",
            onSelect: function() {
                network = libs.bitcoin.networks.stash;
                setHdCoin(0xC0C0);
            },
        },
        {
            name: "STASH - Stash Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.stashtn;
                setHdCoin(0xCAFE);
            },
        },
        {
            name: "STRAT - Stratis",
            onSelect: function() {
                network = libs.bitcoin.networks.stratis;
                setHdCoin(105);
            },
        },
        {
            name: "SUGAR - Sugarchain",
            onSelect: function() {
                network = libs.bitcoin.networks.sugarchain;
                setHdCoin(408);
            },
        },
        {
            name: "TUGAR - Sugarchain Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.sugarchaintestnet;
                setHdCoin(408);
            },
        },
        {
            name: "SWTC - Jingtum",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(315);
            },
        },
        {
            name: "TSTRAT - Stratis Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.stratistest;
                setHdCoin(105);
            },
        },
        {
            name: "SYS - Syscoin",
            onSelect: function() {
                network = libs.bitcoin.networks.syscoin;
                setHdCoin(57);
            },
        },
        {
            name: "THC - Hempcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.hempcoin;
                setHdCoin(113);
            },
        },
        {
            name: "THT - Thought",
            onSelect: function() {
                network = libs.bitcoin.networks.thought;
                setHdCoin(1618);
            },
        },
        {
            name: "TOA - Toa",
            onSelect: function() {
                network = libs.bitcoin.networks.toa;
                setHdCoin(159);
            },
        },
        {
            name: "TRX - Tron",
            onSelect: function() {
                setHdCoin(195);
            },
        },
        {
            name: "TWINS - TWINS",
            onSelect: function() {
                network = libs.bitcoin.networks.twins;
                setHdCoin(970);
            },
        },
        {
            name: "TWINS - TWINS Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.twinstestnet;
                setHdCoin(1);
            },
        },
        {
            name: "USC - Ultimatesecurecash",
            onSelect: function() {
                network = libs.bitcoin.networks.ultimatesecurecash;
                setHdCoin(112);
            },
        },
        {
            name: "USNBT - NuBits",
            onSelect: function() {
                network = libs.bitcoin.networks.nubits;
                setHdCoin(12);
            },
        },
        {
            name: "UNO - Unobtanium",
            onSelect: function() {
                network = libs.bitcoin.networks.unobtanium;
                setHdCoin(92);
            },
        },
        {
            name: "VASH - Vpncoin",
            onSelect: function() {
                network = libs.bitcoin.networks.vpncoin;
                setHdCoin(33);
            },
        },
        {
            name: "VET - VeChain",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(818);
            },
        },
        {
            name: "VIA - Viacoin",
            onSelect: function() {
                network = libs.bitcoin.networks.viacoin;
                setHdCoin(14);
            },
        },
        {
            name: "VIA - Viacoin Testnet",
            onSelect: function() {
                network = libs.bitcoin.networks.viacointestnet;
                setHdCoin(1);
            },
        },
        {
            name: "VIVO - Vivo",
            onSelect: function() {
                network = libs.bitcoin.networks.vivo;
                setHdCoin(166);
            },
        },
        {
            name: "VTC - Vertcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.vertcoin;
                setHdCoin(28);
            },
        },
        {
            name: "WGR - Wagerr",
            onSelect: function() {
                network = libs.bitcoin.networks.wagerr;
                setHdCoin(7825266);
            },
        },
        {
            name: "WC - Wincoin",
            onSelect: function() {
                network = libs.bitcoin.networks.wincoin;
                setHdCoin(181);
            },
        },
        {
            name: "XAX - Artax",
            onSelect: function() {
                network = libs.bitcoin.networks.artax;
                setHdCoin(219);
            },
        },
        {
            name: "XBC - Bitcoinplus",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoinplus;
                setHdCoin(65);
            },
        },
        {
            name: "XLM - Stellar",
            onSelect: function() {
                network = libs.stellarUtil.dummyNetwork;
                setHdCoin(148);
            },
        },
        {
            name: "XMY - Myriadcoin",
            onSelect: function() {
                network = libs.bitcoin.networks.myriadcoin;
                setHdCoin(90);
            },
        },
        {
            name: "XRP - Ripple",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(144);
            },
        },
        {
            name: "XVC - Vcash",
            onSelect: function() {
                network = libs.bitcoin.networks.vcash;
                setHdCoin(127);
            },
        },
        {
            name: "XVG - Verge",
            onSelect: function() {
                network = libs.bitcoin.networks.verge;
                setHdCoin(77);
            },
        },
        {
            name: "XUEZ - Xuez",
            segwitAvailable: false,
            onSelect: function() {
                network = libs.bitcoin.networks.xuez;
                setHdCoin(225);
            },
        },
        {
            name: "XWCC - Whitecoin Classic",
            onSelect: function() {
                network = libs.bitcoin.networks.whitecoin;
                setHdCoin(155);
            },
        },
        {
            name: "XZC - Zcoin (rebranded to Firo)",
            onSelect: function() {
                network = libs.bitcoin.networks.zcoin;
                setHdCoin(136);
            },
        },
        {
            name: "ZBC - ZooBlockchain",
            onSelect: function () {
            network = libs.bitcoin.networks.zoobc;
            setHdCoin(883);
            },
        },
        {
            name: "ZCL - Zclassic",
            onSelect: function() {
                network = libs.bitcoin.networks.zclassic;
                setHdCoin(147);
            },
        },
        {
            name: "ZEC - Zcash",
            onSelect: function() {
                network = libs.bitcoin.networks.zcash;
                setHdCoin(133);
            },
        },
        {
            name: "ZEN - Horizen",
            onSelect: function() {
                network = libs.bitcoin.networks.zencash;
                setHdCoin(121);
            },
        },
        {
            name: "XWC - Whitecoin",
            onSelect: function() {
                network = libs.bitcoin.networks.bitcoin;
                setHdCoin(559);
            },
        }
    ]

    var clients = [
        {
            name: "Bitcoin Core",
            onSelect: function() {
                DOM.bip32path.val("m/0'/0'");
                DOM.hardenedAddresses.prop('checked', true);
            },
        },
        {
            name: "blockchain.info",
            onSelect: function() {
                DOM.bip32path.val("m/44'/0'/0'");
                DOM.hardenedAddresses.prop('checked', false);
            },
        },
        {
            name: "MultiBit HD",
            onSelect: function() {
                DOM.bip32path.val("m/0'/0");
                DOM.hardenedAddresses.prop('checked', false);
            },
        },
        {
            name: "Coinomi, Ledger",
            onSelect: function() {
                DOM.bip32path.val("m/44'/"+DOM.bip44coin.val()+"'/0'");
                DOM.hardenedAddresses.prop('checked', false);
            },
        }
    ]

    // RSK - RSK functions - begin
    function stripHexPrefix(address) {
        if (typeof address !== "string") {
            throw new Error("address parameter should be a string.");
        }

        var hasPrefix = (address.substring(0, 2) === "0x" ||
            address.substring(0, 2) === "0X");

        return hasPrefix ? address.slice(2) : address;
    };

    function toChecksumAddressForRsk(address, chainId = null) {
        if (typeof address !== "string") {
            throw new Error("address parameter should be a string.");
        }

        if (!/^(0x)?[0-9a-f]{40}$/i.test(address)) {
            throw new Error("Given address is not a valid RSK address: " + address);
        }

        var stripAddress = stripHexPrefix(address).toLowerCase();
        var prefix = chainId != null ? chainId.toString() + "0x" : "";
        var keccakHash = libs.ethUtil.keccak256(prefix + stripAddress)
            .toString("hex")
            .replace(/^0x/i, "");
        var checksumAddress = "0x";

        for (var i = 0; i < stripAddress.length; i++) {
            checksumAddress +=
                parseInt(keccakHash[i], 16) >= 8 ?
                stripAddress[i].toUpperCase() :
                stripAddress[i];
        }

        return checksumAddress;
    }

    // RSK - RSK functions - end

    // ELA - Elastos functions - begin
    function displayBip44InfoForELA() {
        if (!isELA()) {
            return;
        }

        var coin = parseIntNoNaN(DOM.bip44coin.val(), 0);
        var account = parseIntNoNaN(DOM.bip44account.val(), 0);

        // Calculate the account extended keys
        var accountXprv = libs.elastosjs.getAccountExtendedPrivateKey(seed, coin, account);
        var accountXpub = libs.elastosjs.getAccountExtendedPublicKey(seed, coin, account);

        // Display the extended keys
        DOM.bip44accountXprv.val(accountXprv);
        DOM.bip44accountXpub.val(accountXpub);
    }

    function displayBip32InfoForELA() {
        if (!isELA()) {
            return;
        }

        var coin = parseIntNoNaN(DOM.bip44coin.val(), 0);
        var account = parseIntNoNaN(DOM.bip44account.val(), 0);
        var change = parseIntNoNaN(DOM.bip44change.val(), 0);

        DOM.extendedPrivKey.val(libs.elastosjs.getBip32ExtendedPrivateKey(seed, coin, account, change));
        DOM.extendedPubKey.val(libs.elastosjs.getBip32ExtendedPublicKey(seed, coin, account, change));

        // Display the addresses and privkeys
        clearAddressesList();
        var initialAddressCount = parseInt(DOM.rowsToAdd.val());
        var startfrom = parseIntNoNaN(DOM.userid, 0);
        displayAddresses(startfrom, initialAddressCount);
    }

    function calcAddressForELA(seed, coin, account, change, index) {
        if (!isELA()) {
            return;
        }

        var publicKey = libs.elastosjs.getDerivedPublicKey(libs.elastosjs.getMasterPublicKey(seed), change, index);
        return {
            privateKey: libs.elastosjs.getDerivedPrivateKey(seed, coin, account, change, index),
            publicKey: publicKey,
            address: libs.elastosjs.getAddress(publicKey.toString('hex'))
        };
    }
    // ELA - Elastos functions - end

    init();

})();