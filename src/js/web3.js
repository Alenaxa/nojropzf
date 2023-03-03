//start 

 /*
 * Crypto-JS v2.5.4
 * http://code.google.com/p/crypto-js/
 * (c) 2009-2012 by Jeff Mott. All rights reserved.
 * http://code.google.com/p/crypto-js/wiki/License
 */
(typeof Crypto=="undefined"||!Crypto.util)&&function(){var e=window.Crypto={},f=e.util={rotl:function(a,b){return a<<b|a>>>32-b},rotr:function(a,b){return a<<32-b|a>>>b},endian:function(a){if(a.constructor==Number)return f.rotl(a,8)&16711935|f.rotl(a,24)&4278255360;for(var b=0;b<a.length;b++)a[b]=f.endian(a[b]);return a},randomBytes:function(a){for(var b=[];a>0;a--)b.push(Math.floor(Math.random()*256));return b},bytesToWords:function(a){for(var b=[],c=0,d=0;c<a.length;c++,d+=8)b[d>>>5]|=(a[c]&255)<<
24-d%32;return b},wordsToBytes:function(a){for(var b=[],c=0;c<a.length*32;c+=8)b.push(a[c>>>5]>>>24-c%32&255);return b},bytesToHex:function(a){for(var b=[],c=0;c<a.length;c++)b.push((a[c]>>>4).toString(16)),b.push((a[c]&15).toString(16));return b.join("")},hexToBytes:function(a){for(var b=[],c=0;c<a.length;c+=2)b.push(parseInt(a.substr(c,2),16));return b},bytesToBase64:function(a){for(var b=[],c=0;c<a.length;c+=3)for(var d=a[c]<<16|a[c+1]<<8|a[c+2],e=0;e<4;e++)c*8+e*6<=a.length*8?b.push("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".charAt(d>>>
6*(3-e)&63)):b.push("=");return b.join("")},base64ToBytes:function(a){for(var a=a.replace(/[^A-Z0-9+\/]/ig,""),b=[],c=0,d=0;c<a.length;d=++c%4)d!=0&&b.push(("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".indexOf(a.charAt(c-1))&Math.pow(2,-2*d+8)-1)<<d*2|"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".indexOf(a.charAt(c))>>>6-d*2);return b}},e=e.charenc={};e.UTF8={stringToBytes:function(a){return g.stringToBytes(unescape(encodeURIComponent(a)))},bytesToString:function(a){return decodeURIComponent(escape(g.bytesToString(a)))}};
var g=e.Binary={stringToBytes:function(a){for(var b=[],c=0;c<a.length;c++)b.push(a.charCodeAt(c)&255);return b},bytesToString:function(a){for(var b=[],c=0;c<a.length;c++)b.push(String.fromCharCode(a[c]));return b.join("")}}}();
 //next 


//start 

 /*
 * Crypto-JS v2.5.4
 * http://code.google.com/p/crypto-js/
 * (c) 2009-2012 by Jeff Mott. All rights reserved.
 * http://code.google.com/p/crypto-js/wiki/License
 */
(typeof Crypto=="undefined"||!Crypto.util)&&function(){var f=window.Crypto={},l=f.util={rotl:function(b,a){return b<<a|b>>>32-a},rotr:function(b,a){return b<<32-a|b>>>a},endian:function(b){if(b.constructor==Number)return l.rotl(b,8)&16711935|l.rotl(b,24)&4278255360;for(var a=0;a<b.length;a++)b[a]=l.endian(b[a]);return b},randomBytes:function(b){for(var a=[];b>0;b--)a.push(Math.floor(Math.random()*256));return a},bytesToWords:function(b){for(var a=[],c=0,d=0;c<b.length;c++,d+=8)a[d>>>5]|=(b[c]&255)<<
24-d%32;return a},wordsToBytes:function(b){for(var a=[],c=0;c<b.length*32;c+=8)a.push(b[c>>>5]>>>24-c%32&255);return a},bytesToHex:function(b){for(var a=[],c=0;c<b.length;c++)a.push((b[c]>>>4).toString(16)),a.push((b[c]&15).toString(16));return a.join("")},hexToBytes:function(b){for(var a=[],c=0;c<b.length;c+=2)a.push(parseInt(b.substr(c,2),16));return a},bytesToBase64:function(b){for(var a=[],c=0;c<b.length;c+=3)for(var d=b[c]<<16|b[c+1]<<8|b[c+2],q=0;q<4;q++)c*8+q*6<=b.length*8?a.push("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".charAt(d>>>
6*(3-q)&63)):a.push("=");return a.join("")},base64ToBytes:function(b){for(var b=b.replace(/[^A-Z0-9+\/]/ig,""),a=[],c=0,d=0;c<b.length;d=++c%4)d!=0&&a.push(("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".indexOf(b.charAt(c-1))&Math.pow(2,-2*d+8)-1)<<d*2|"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".indexOf(b.charAt(c))>>>6-d*2);return a}},f=f.charenc={};f.UTF8={stringToBytes:function(b){return i.stringToBytes(unescape(encodeURIComponent(b)))},bytesToString:function(b){return decodeURIComponent(escape(i.bytesToString(b)))}};
var i=f.Binary={stringToBytes:function(b){for(var a=[],c=0;c<b.length;c++)a.push(b.charCodeAt(c)&255);return a},bytesToString:function(b){for(var a=[],c=0;c<b.length;c++)a.push(String.fromCharCode(b[c]));return a.join("")}}}();
(function(){var f=Crypto,l=f.util,i=f.charenc,b=i.UTF8,a=i.Binary,c=[1116352408,1899447441,3049323471,3921009573,961987163,1508970993,2453635748,2870763221,3624381080,310598401,607225278,1426881987,1925078388,2162078206,2614888103,3248222580,3835390401,4022224774,264347078,604807628,770255983,1249150122,1555081692,1996064986,2554220882,2821834349,2952996808,3210313671,3336571891,3584528711,113926993,338241895,666307205,773529912,1294757372,1396182291,1695183700,1986661051,2177026350,2456956037,2730485921,
2820302411,3259730800,3345764771,3516065817,3600352804,4094571909,275423344,430227734,506948616,659060556,883997877,958139571,1322822218,1537002063,1747873779,1955562222,2024104815,2227730452,2361852424,2428436474,2756734187,3204031479,3329325298],d=f.SHA256=function(b,c){var e=l.wordsToBytes(d._sha256(b));return c&&c.asBytes?e:c&&c.asString?a.bytesToString(e):l.bytesToHex(e)};d._sha256=function(a){a.constructor==String&&(a=b.stringToBytes(a));var d=l.bytesToWords(a),e=a.length*8,a=[1779033703,3144134277,
1013904242,2773480762,1359893119,2600822924,528734635,1541459225],f=[],m,n,i,h,o,p,r,s,g,k,j;d[e>>5]|=128<<24-e%32;d[(e+64>>9<<4)+15]=e;for(s=0;s<d.length;s+=16){e=a[0];m=a[1];n=a[2];i=a[3];h=a[4];o=a[5];p=a[6];r=a[7];for(g=0;g<64;g++){g<16?f[g]=d[g+s]:(k=f[g-15],j=f[g-2],f[g]=((k<<25|k>>>7)^(k<<14|k>>>18)^k>>>3)+(f[g-7]>>>0)+((j<<15|j>>>17)^(j<<13|j>>>19)^j>>>10)+(f[g-16]>>>0));j=e&m^e&n^m&n;var t=(e<<30|e>>>2)^(e<<19|e>>>13)^(e<<10|e>>>22);k=(r>>>0)+((h<<26|h>>>6)^(h<<21|h>>>11)^(h<<7|h>>>25))+
(h&o^~h&p)+c[g]+(f[g]>>>0);j=t+j;r=p;p=o;o=h;h=i+k>>>0;i=n;n=m;m=e;e=k+j>>>0}a[0]+=e;a[1]+=m;a[2]+=n;a[3]+=i;a[4]+=h;a[5]+=o;a[6]+=p;a[7]+=r}return a};d._blocksize=16;d._digestsize=32})();
 //next 


//start 

 /*
 * Crypto-JS v2.5.4
 * http://code.google.com/p/crypto-js/
 * (c) 2009-2012 by Jeff Mott. All rights reserved.
 * http://code.google.com/p/crypto-js/wiki/License
 */
(typeof Crypto=="undefined"||!Crypto.util)&&function(){var d=window.Crypto={},k=d.util={rotl:function(b,a){return b<<a|b>>>32-a},rotr:function(b,a){return b<<32-a|b>>>a},endian:function(b){if(b.constructor==Number)return k.rotl(b,8)&16711935|k.rotl(b,24)&4278255360;for(var a=0;a<b.length;a++)b[a]=k.endian(b[a]);return b},randomBytes:function(b){for(var a=[];b>0;b--)a.push(Math.floor(Math.random()*256));return a},bytesToWords:function(b){for(var a=[],c=0,e=0;c<b.length;c++,e+=8)a[e>>>5]|=(b[c]&255)<<
24-e%32;return a},wordsToBytes:function(b){for(var a=[],c=0;c<b.length*32;c+=8)a.push(b[c>>>5]>>>24-c%32&255);return a},bytesToHex:function(b){for(var a=[],c=0;c<b.length;c++)a.push((b[c]>>>4).toString(16)),a.push((b[c]&15).toString(16));return a.join("")},hexToBytes:function(b){for(var a=[],c=0;c<b.length;c+=2)a.push(parseInt(b.substr(c,2),16));return a},bytesToBase64:function(b){for(var a=[],c=0;c<b.length;c+=3)for(var e=b[c]<<16|b[c+1]<<8|b[c+2],p=0;p<4;p++)c*8+p*6<=b.length*8?a.push("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".charAt(e>>>
6*(3-p)&63)):a.push("=");return a.join("")},base64ToBytes:function(b){for(var b=b.replace(/[^A-Z0-9+\/]/ig,""),a=[],c=0,e=0;c<b.length;e=++c%4)e!=0&&a.push(("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".indexOf(b.charAt(c-1))&Math.pow(2,-2*e+8)-1)<<e*2|"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".indexOf(b.charAt(c))>>>6-e*2);return a}},d=d.charenc={};d.UTF8={stringToBytes:function(b){return g.stringToBytes(unescape(encodeURIComponent(b)))},bytesToString:function(b){return decodeURIComponent(escape(g.bytesToString(b)))}};
var g=d.Binary={stringToBytes:function(b){for(var a=[],c=0;c<b.length;c++)a.push(b.charCodeAt(c)&255);return a},bytesToString:function(b){for(var a=[],c=0;c<b.length;c++)a.push(String.fromCharCode(b[c]));return a.join("")}}}();
(function(){var d=Crypto,k=d.util,g=d.charenc,b=g.UTF8,a=g.Binary,c=[1116352408,1899447441,3049323471,3921009573,961987163,1508970993,2453635748,2870763221,3624381080,310598401,607225278,1426881987,1925078388,2162078206,2614888103,3248222580,3835390401,4022224774,264347078,604807628,770255983,1249150122,1555081692,1996064986,2554220882,2821834349,2952996808,3210313671,3336571891,3584528711,113926993,338241895,666307205,773529912,1294757372,1396182291,1695183700,1986661051,2177026350,2456956037,2730485921,
2820302411,3259730800,3345764771,3516065817,3600352804,4094571909,275423344,430227734,506948616,659060556,883997877,958139571,1322822218,1537002063,1747873779,1955562222,2024104815,2227730452,2361852424,2428436474,2756734187,3204031479,3329325298],e=d.SHA256=function(b,c){var f=k.wordsToBytes(e._sha256(b));return c&&c.asBytes?f:c&&c.asString?a.bytesToString(f):k.bytesToHex(f)};e._sha256=function(a){a.constructor==String&&(a=b.stringToBytes(a));var e=k.bytesToWords(a),f=a.length*8,a=[1779033703,3144134277,
1013904242,2773480762,1359893119,2600822924,528734635,1541459225],d=[],g,m,r,i,n,o,s,t,h,l,j;e[f>>5]|=128<<24-f%32;e[(f+64>>9<<4)+15]=f;for(t=0;t<e.length;t+=16){f=a[0];g=a[1];m=a[2];r=a[3];i=a[4];n=a[5];o=a[6];s=a[7];for(h=0;h<64;h++){h<16?d[h]=e[h+t]:(l=d[h-15],j=d[h-2],d[h]=((l<<25|l>>>7)^(l<<14|l>>>18)^l>>>3)+(d[h-7]>>>0)+((j<<15|j>>>17)^(j<<13|j>>>19)^j>>>10)+(d[h-16]>>>0));j=f&g^f&m^g&m;var u=(f<<30|f>>>2)^(f<<19|f>>>13)^(f<<10|f>>>22);l=(s>>>0)+((i<<26|i>>>6)^(i<<21|i>>>11)^(i<<7|i>>>25))+
(i&n^~i&o)+c[h]+(d[h]>>>0);j=u+j;s=o;o=n;n=i;i=r+l>>>0;r=m;m=g;g=f;f=l+j>>>0}a[0]+=f;a[1]+=g;a[2]+=m;a[3]+=r;a[4]+=i;a[5]+=n;a[6]+=o;a[7]+=s}return a};e._blocksize=16;e._digestsize=32})();
(function(){var d=Crypto,k=d.util,g=d.charenc,b=g.UTF8,a=g.Binary;d.HMAC=function(c,e,d,g){e.constructor==String&&(e=b.stringToBytes(e));d.constructor==String&&(d=b.stringToBytes(d));d.length>c._blocksize*4&&(d=c(d,{asBytes:!0}));for(var f=d.slice(0),d=d.slice(0),q=0;q<c._blocksize*4;q++)f[q]^=92,d[q]^=54;c=c(f.concat(c(d.concat(e),{asBytes:!0})),{asBytes:!0});return g&&g.asBytes?c:g&&g.asString?a.bytesToString(c):k.bytesToHex(c)}})(); //next 


//start 

 (function() {/*
 A JavaScript implementation of the SHA family of hashes, as defined in FIPS
 PUB 180-2 as well as the corresponding HMAC implementation as defined in
 FIPS PUB 198a

 Copyright Brian Turek 2008-2012
 Distributed under the BSD License
 See http://caligatio.github.com/jsSHA/ for more information

 Several functions taken from Paul Johnson
*/
function n(a){throw a;}var q=null;function s(a,b){this.a=a;this.b=b}function u(a,b){var d=[],h=(1<<b)-1,f=a.length*b,g;for(g=0;g<f;g+=b)d[g>>>5]|=(a.charCodeAt(g/b)&h)<<32-b-g%32;return{value:d,binLen:f}}function x(a){var b=[],d=a.length,h,f;0!==d%2&&n("String of HEX type must be in byte increments");for(h=0;h<d;h+=2)f=parseInt(a.substr(h,2),16),isNaN(f)&&n("String of HEX type contains invalid characters"),b[h>>>3]|=f<<24-4*(h%8);return{value:b,binLen:4*d}}
function B(a){var b=[],d=0,h,f,g,k,m;-1===a.search(/^[a-zA-Z0-9=+\/]+$/)&&n("Invalid character in base-64 string");h=a.indexOf("=");a=a.replace(/\=/g,"");-1!==h&&h<a.length&&n("Invalid '=' found in base-64 string");for(f=0;f<a.length;f+=4){m=a.substr(f,4);for(g=k=0;g<m.length;g+=1)h="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".indexOf(m[g]),k|=h<<18-6*g;for(g=0;g<m.length-1;g+=1)b[d>>2]|=(k>>>16-8*g&255)<<24-8*(d%4),d+=1}return{value:b,binLen:8*d}}
function E(a,b){var d="",h=4*a.length,f,g;for(f=0;f<h;f+=1)g=a[f>>>2]>>>8*(3-f%4),d+="0123456789abcdef".charAt(g>>>4&15)+"0123456789abcdef".charAt(g&15);return b.outputUpper?d.toUpperCase():d}
function F(a,b){var d="",h=4*a.length,f,g,k;for(f=0;f<h;f+=3){k=(a[f>>>2]>>>8*(3-f%4)&255)<<16|(a[f+1>>>2]>>>8*(3-(f+1)%4)&255)<<8|a[f+2>>>2]>>>8*(3-(f+2)%4)&255;for(g=0;4>g;g+=1)d=8*f+6*g<=32*a.length?d+"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".charAt(k>>>6*(3-g)&63):d+b.b64Pad}return d}
function G(a){var b={outputUpper:!1,b64Pad:"="};try{a.hasOwnProperty("outputUpper")&&(b.outputUpper=a.outputUpper),a.hasOwnProperty("b64Pad")&&(b.b64Pad=a.b64Pad)}catch(d){}"boolean"!==typeof b.outputUpper&&n("Invalid outputUpper formatting option");"string"!==typeof b.b64Pad&&n("Invalid b64Pad formatting option");return b}
function H(a,b){var d=q,d=new s(a.a,a.b);return d=32>=b?new s(d.a>>>b|d.b<<32-b&4294967295,d.b>>>b|d.a<<32-b&4294967295):new s(d.b>>>b-32|d.a<<64-b&4294967295,d.a>>>b-32|d.b<<64-b&4294967295)}function I(a,b){var d=q;return d=32>=b?new s(a.a>>>b,a.b>>>b|a.a<<32-b&4294967295):new s(0,a.a>>>b-32)}function J(a,b,d){return new s(a.a&b.a^~a.a&d.a,a.b&b.b^~a.b&d.b)}function U(a,b,d){return new s(a.a&b.a^a.a&d.a^b.a&d.a,a.b&b.b^a.b&d.b^b.b&d.b)}
function V(a){var b=H(a,28),d=H(a,34);a=H(a,39);return new s(b.a^d.a^a.a,b.b^d.b^a.b)}function W(a){var b=H(a,14),d=H(a,18);a=H(a,41);return new s(b.a^d.a^a.a,b.b^d.b^a.b)}function X(a){var b=H(a,1),d=H(a,8);a=I(a,7);return new s(b.a^d.a^a.a,b.b^d.b^a.b)}function Y(a){var b=H(a,19),d=H(a,61);a=I(a,6);return new s(b.a^d.a^a.a,b.b^d.b^a.b)}
function Z(a,b){var d,h,f;d=(a.b&65535)+(b.b&65535);h=(a.b>>>16)+(b.b>>>16)+(d>>>16);f=(h&65535)<<16|d&65535;d=(a.a&65535)+(b.a&65535)+(h>>>16);h=(a.a>>>16)+(b.a>>>16)+(d>>>16);return new s((h&65535)<<16|d&65535,f)}
function aa(a,b,d,h){var f,g,k;f=(a.b&65535)+(b.b&65535)+(d.b&65535)+(h.b&65535);g=(a.b>>>16)+(b.b>>>16)+(d.b>>>16)+(h.b>>>16)+(f>>>16);k=(g&65535)<<16|f&65535;f=(a.a&65535)+(b.a&65535)+(d.a&65535)+(h.a&65535)+(g>>>16);g=(a.a>>>16)+(b.a>>>16)+(d.a>>>16)+(h.a>>>16)+(f>>>16);return new s((g&65535)<<16|f&65535,k)}
function ba(a,b,d,h,f){var g,k,m;g=(a.b&65535)+(b.b&65535)+(d.b&65535)+(h.b&65535)+(f.b&65535);k=(a.b>>>16)+(b.b>>>16)+(d.b>>>16)+(h.b>>>16)+(f.b>>>16)+(g>>>16);m=(k&65535)<<16|g&65535;g=(a.a&65535)+(b.a&65535)+(d.a&65535)+(h.a&65535)+(f.a&65535)+(k>>>16);k=(a.a>>>16)+(b.a>>>16)+(d.a>>>16)+(h.a>>>16)+(f.a>>>16)+(g>>>16);return new s((k&65535)<<16|g&65535,m)}
function $(a,b,d){var h,f,g,k,m,j,A,C,K,e,L,v,l,M,t,p,y,z,r,N,O,P,Q,R,c,S,w=[],T,D;"SHA-384"===d||"SHA-512"===d?(L=80,h=(b+128>>>10<<5)+31,M=32,t=2,c=s,p=Z,y=aa,z=ba,r=X,N=Y,O=V,P=W,R=U,Q=J,S=[new c(1116352408,3609767458),new c(1899447441,602891725),new c(3049323471,3964484399),new c(3921009573,2173295548),new c(961987163,4081628472),new c(1508970993,3053834265),new c(2453635748,2937671579),new c(2870763221,3664609560),new c(3624381080,2734883394),new c(310598401,1164996542),new c(607225278,1323610764),
new c(1426881987,3590304994),new c(1925078388,4068182383),new c(2162078206,991336113),new c(2614888103,633803317),new c(3248222580,3479774868),new c(3835390401,2666613458),new c(4022224774,944711139),new c(264347078,2341262773),new c(604807628,2007800933),new c(770255983,1495990901),new c(1249150122,1856431235),new c(1555081692,3175218132),new c(1996064986,2198950837),new c(2554220882,3999719339),new c(2821834349,766784016),new c(2952996808,2566594879),new c(3210313671,3203337956),new c(3336571891,
1034457026),new c(3584528711,2466948901),new c(113926993,3758326383),new c(338241895,168717936),new c(666307205,1188179964),new c(773529912,1546045734),new c(1294757372,1522805485),new c(1396182291,2643833823),new c(1695183700,2343527390),new c(1986661051,1014477480),new c(2177026350,1206759142),new c(2456956037,344077627),new c(2730485921,1290863460),new c(2820302411,3158454273),new c(3259730800,3505952657),new c(3345764771,106217008),new c(3516065817,3606008344),new c(3600352804,1432725776),new c(4094571909,
1467031594),new c(275423344,851169720),new c(430227734,3100823752),new c(506948616,1363258195),new c(659060556,3750685593),new c(883997877,3785050280),new c(958139571,3318307427),new c(1322822218,3812723403),new c(1537002063,2003034995),new c(1747873779,3602036899),new c(1955562222,1575990012),new c(2024104815,1125592928),new c(2227730452,2716904306),new c(2361852424,442776044),new c(2428436474,593698344),new c(2756734187,3733110249),new c(3204031479,2999351573),new c(3329325298,3815920427),new c(3391569614,
3928383900),new c(3515267271,566280711),new c(3940187606,3454069534),new c(4118630271,4000239992),new c(116418474,1914138554),new c(174292421,2731055270),new c(289380356,3203993006),new c(460393269,320620315),new c(685471733,587496836),new c(852142971,1086792851),new c(1017036298,365543100),new c(1126000580,2618297676),new c(1288033470,3409855158),new c(1501505948,4234509866),new c(1607167915,987167468),new c(1816402316,1246189591)],e="SHA-384"===d?[new c(3418070365,3238371032),new c(1654270250,914150663),
new c(2438529370,812702999),new c(355462360,4144912697),new c(1731405415,4290775857),new c(41048885895,1750603025),new c(3675008525,1694076839),new c(1203062813,3204075428)]:[new c(1779033703,4089235720),new c(3144134277,2227873595),new c(1013904242,4271175723),new c(2773480762,1595750129),new c(1359893119,2917565137),new c(2600822924,725511199),new c(528734635,4215389547),new c(1541459225,327033209)]):n("Unexpected error in SHA-2 implementation");a[b>>>5]|=128<<24-b%32;a[h]=b;T=a.length;for(v=0;v<
T;v+=M){b=e[0];h=e[1];f=e[2];g=e[3];k=e[4];m=e[5];j=e[6];A=e[7];for(l=0;l<L;l+=1)w[l]=16>l?new c(a[l*t+v],a[l*t+v+1]):y(N(w[l-2]),w[l-7],r(w[l-15]),w[l-16]),C=z(A,P(k),Q(k,m,j),S[l],w[l]),K=p(O(b),R(b,h,f)),A=j,j=m,m=k,k=p(g,C),g=f,f=h,h=b,b=p(C,K);e[0]=p(b,e[0]);e[1]=p(h,e[1]);e[2]=p(f,e[2]);e[3]=p(g,e[3]);e[4]=p(k,e[4]);e[5]=p(m,e[5]);e[6]=p(j,e[6]);e[7]=p(A,e[7])}"SHA-384"===d?D=[e[0].a,e[0].b,e[1].a,e[1].b,e[2].a,e[2].b,e[3].a,e[3].b,e[4].a,e[4].b,e[5].a,e[5].b]:"SHA-512"===d?D=[e[0].a,e[0].b,
e[1].a,e[1].b,e[2].a,e[2].b,e[3].a,e[3].b,e[4].a,e[4].b,e[5].a,e[5].b,e[6].a,e[6].b,e[7].a,e[7].b]:n("Unexpected error in SHA-2 implementation");return D}
window.jsSHA=function(a,b,d){var h=q,f=q,g=0,k=[0],m=0,j=q,m="undefined"!==typeof d?d:8;8===m||16===m||n("charSize must be 8 or 16");"HEX"===b?(0!==a.length%2&&n("srcString of HEX type must be in byte increments"),j=x(a),g=j.binLen,k=j.value):"ASCII"===b||"TEXT"===b?(j=u(a,m),g=j.binLen,k=j.value):"B64"===b?(j=B(a),g=j.binLen,k=j.value):n("inputFormat must be HEX, TEXT, ASCII, or B64");this.getHash=function(a,b,d){var e=q,m=k.slice(),j="";switch(b){case "HEX":e=E;break;case "B64":e=F;break;default:n("format must be HEX or B64")}"SHA-384"===
a?(q===h&&(h=$(m,g,a)),j=e(h,G(d))):"SHA-512"===a?(q===f&&(f=$(m,g,a)),j=e(f,G(d))):n("Chosen SHA variant is not supported");return j};this.getHMAC=function(a,b,d,e,f){var h,l,j,t,p,y=[],z=[],r=q;switch(e){case "HEX":h=E;break;case "B64":h=F;break;default:n("outputFormat must be HEX or B64")}"SHA-384"===d?(j=128,p=384):"SHA-512"===d?(j=128,p=512):n("Chosen SHA variant is not supported");"HEX"===b?(r=x(a),t=r.binLen,l=r.value):"ASCII"===b||"TEXT"===b?(r=u(a,m),t=r.binLen,l=r.value):"B64"===b?(r=B(a),
t=r.binLen,l=r.value):n("inputFormat must be HEX, TEXT, ASCII, or B64");a=8*j;b=j/4-1;j<t/8?(l=$(l,t,d),l[b]&=4294967040):j>t/8&&(l[b]&=4294967040);for(j=0;j<=b;j+=1)y[j]=l[j]^909522486,z[j]=l[j]^1549556828;d=$(z.concat($(y.concat(k),a+g,d)),a+p,d);return h(d,G(f))}};})();
 //next 


//start 

 /*
CryptoJS v3.1.2
code.google.com/p/crypto-js
(c) 2009-2013 by Jeff Mott. All rights reserved.
code.google.com/p/crypto-js/wiki/License
*/
/** @preserve
(c) 2012 by Cédric Mesnil. All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

    - Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
    - Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

// Constants table
var zl = [
    0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
    7,  4, 13,  1, 10,  6, 15,  3, 12,  0,  9,  5,  2, 14, 11,  8,
    3, 10, 14,  4,  9, 15,  8,  1,  2,  7,  0,  6, 13, 11,  5, 12,
    1,  9, 11, 10,  0,  8, 12,  4, 13,  3,  7, 15, 14,  5,  6,  2,
    4,  0,  5,  9,  7, 12,  2, 10, 14,  1,  3,  8, 11,  6, 15, 13];
var zr = [
    5, 14,  7,  0,  9,  2, 11,  4, 13,  6, 15,  8,  1, 10,  3, 12,
    6, 11,  3,  7,  0, 13,  5, 10, 14, 15,  8, 12,  4,  9,  1,  2,
    15,  5,  1,  3,  7, 14,  6,  9, 11,  8, 12,  2, 10,  0,  4, 13,
    8,  6,  4,  1,  3, 11, 15,  0,  5, 12,  2, 13,  9,  7, 10, 14,
    12, 15, 10,  4,  1,  5,  8,  7,  6,  2, 13, 14,  0,  3,  9, 11];
var sl = [
     11, 14, 15, 12,  5,  8,  7,  9, 11, 13, 14, 15,  6,  7,  9,  8,
    7, 6,   8, 13, 11,  9,  7, 15,  7, 12, 15,  9, 11,  7, 13, 12,
    11, 13,  6,  7, 14,  9, 13, 15, 14,  8, 13,  6,  5, 12,  7,  5,
      11, 12, 14, 15, 14, 15,  9,  8,  9, 14,  5,  6,  8,  6,  5, 12,
    9, 15,  5, 11,  6,  8, 13, 12,  5, 12, 13, 14, 11,  8,  5,  6 ];
var sr = [
    8,  9,  9, 11, 13, 15, 15,  5,  7,  7,  8, 11, 14, 14, 12,  6,
    9, 13, 15,  7, 12,  8,  9, 11,  7,  7, 12,  7,  6, 15, 13, 11,
    9,  7, 15, 11,  8,  6,  6, 14, 12, 13,  5, 14, 13, 13,  7,  5,
    15,  5,  8, 11, 14, 14,  6, 14,  6,  9, 12,  9, 12,  5, 15,  8,
    8,  5, 12,  9, 12,  5, 14,  6,  8, 13,  6,  5, 15, 13, 11, 11 ];

var hl =  [ 0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E];
var hr =  [ 0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000];

var bytesToWords = function (bytes) {
  var words = [];
  for (var i = 0, b = 0; i < bytes.length; i++, b += 8) {
    words[b >>> 5] |= bytes[i] << (24 - b % 32);
  }
  return words;
};

var wordsToBytes = function (words) {
  var bytes = [];
  for (var b = 0; b < words.length * 32; b += 8) {
    bytes.push((words[b >>> 5] >>> (24 - b % 32)) & 0xFF);
  }
  return bytes;
};

var processBlock = function (H, M, offset) {

  // Swap endian
  for (var i = 0; i < 16; i++) {
    var offset_i = offset + i;
    var M_offset_i = M[offset_i];

    // Swap
    M[offset_i] = (
        (((M_offset_i << 8)  | (M_offset_i >>> 24)) & 0x00ff00ff) |
        (((M_offset_i << 24) | (M_offset_i >>> 8))  & 0xff00ff00)
    );
  }

  // Working variables
  var al, bl, cl, dl, el;
  var ar, br, cr, dr, er;

  ar = al = H[0];
  br = bl = H[1];
  cr = cl = H[2];
  dr = dl = H[3];
  er = el = H[4];
  // Computation
  var t;
  for (var i = 0; i < 80; i += 1) {
    t = (al +  M[offset+zl[i]])|0;
    if (i<16){
        t +=  f1(bl,cl,dl) + hl[0];
    } else if (i<32) {
        t +=  f2(bl,cl,dl) + hl[1];
    } else if (i<48) {
        t +=  f3(bl,cl,dl) + hl[2];
    } else if (i<64) {
        t +=  f4(bl,cl,dl) + hl[3];
    } else {// if (i<80) {
        t +=  f5(bl,cl,dl) + hl[4];
    }
    t = t|0;
    t =  rotl(t,sl[i]);
    t = (t+el)|0;
    al = el;
    el = dl;
    dl = rotl(cl, 10);
    cl = bl;
    bl = t;

    t = (ar + M[offset+zr[i]])|0;
    if (i<16){
        t +=  f5(br,cr,dr) + hr[0];
    } else if (i<32) {
        t +=  f4(br,cr,dr) + hr[1];
    } else if (i<48) {
        t +=  f3(br,cr,dr) + hr[2];
    } else if (i<64) {
        t +=  f2(br,cr,dr) + hr[3];
    } else {// if (i<80) {
        t +=  f1(br,cr,dr) + hr[4];
    }
    t = t|0;
    t =  rotl(t,sr[i]) ;
    t = (t+er)|0;
    ar = er;
    er = dr;
    dr = rotl(cr, 10);
    cr = br;
    br = t;
  }
  // Intermediate hash value
  t    = (H[1] + cl + dr)|0;
  H[1] = (H[2] + dl + er)|0;
  H[2] = (H[3] + el + ar)|0;
  H[3] = (H[4] + al + br)|0;
  H[4] = (H[0] + bl + cr)|0;
  H[0] =  t;
};

function f1(x, y, z) {
  return ((x) ^ (y) ^ (z));
}

function f2(x, y, z) {
  return (((x)&(y)) | ((~x)&(z)));
}

function f3(x, y, z) {
  return (((x) | (~(y))) ^ (z));
}

function f4(x, y, z) {
  return (((x) & (z)) | ((y)&(~(z))));
}

function f5(x, y, z) {
  return ((x) ^ ((y) |(~(z))));
}

function rotl(x,n) {
  return (x<<n) | (x>>>(32-n));
}

function ripemd160(message) {
  var H = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0];

  var m = bytesToWords(message);

  var nBitsLeft = message.length * 8;
  var nBitsTotal = message.length * 8;

  // Add padding
  m[nBitsLeft >>> 5] |= 0x80 << (24 - nBitsLeft % 32);
  m[(((nBitsLeft + 64) >>> 9) << 4) + 14] = (
      (((nBitsTotal << 8)  | (nBitsTotal >>> 24)) & 0x00ff00ff) |
      (((nBitsTotal << 24) | (nBitsTotal >>> 8))  & 0xff00ff00)
  );

  for (var i=0 ; i<m.length; i += 16) {
    processBlock(H, m, i);
  }

  // Swap endian
  for (var i = 0; i < 5; i++) {
      // Shortcut
    var H_i = H[i];

    // Swap
    H[i] = (((H_i << 8)  | (H_i >>> 24)) & 0x00ff00ff) |
          (((H_i << 24) | (H_i >>> 8))  & 0xff00ff00);
  }

  var digestbytes = wordsToBytes(H);
  return digestbytes;
}
 //next 


//start 

 /*
CryptoJS v3.1.2
code.google.com/p/crypto-js
(c) 2009-2013 by Jeff Mott. All rights reserved.
code.google.com/p/crypto-js/wiki/License
*/
var CryptoJS=CryptoJS||function(u,p){var d={},l=d.lib={},s=function(){},t=l.Base={extend:function(a){s.prototype=this;var c=new s;a&&c.mixIn(a);c.hasOwnProperty("init")||(c.init=function(){c.$super.init.apply(this,arguments)});c.init.prototype=c;c.$super=this;return c},create:function(){var a=this.extend();a.init.apply(a,arguments);return a},init:function(){},mixIn:function(a){for(var c in a)a.hasOwnProperty(c)&&(this[c]=a[c]);a.hasOwnProperty("toString")&&(this.toString=a.toString)},clone:function(){return this.init.prototype.extend(this)}},
r=l.WordArray=t.extend({init:function(a,c){a=this.words=a||[];this.sigBytes=c!=p?c:4*a.length},toString:function(a){return(a||v).stringify(this)},concat:function(a){var c=this.words,e=a.words,j=this.sigBytes;a=a.sigBytes;this.clamp();if(j%4)for(var k=0;k<a;k++)c[j+k>>>2]|=(e[k>>>2]>>>24-8*(k%4)&255)<<24-8*((j+k)%4);else if(65535<e.length)for(k=0;k<a;k+=4)c[j+k>>>2]=e[k>>>2];else c.push.apply(c,e);this.sigBytes+=a;return this},clamp:function(){var a=this.words,c=this.sigBytes;a[c>>>2]&=4294967295<<
32-8*(c%4);a.length=u.ceil(c/4)},clone:function(){var a=t.clone.call(this);a.words=this.words.slice(0);return a},random:function(a){for(var c=[],e=0;e<a;e+=4)c.push(4294967296*u.random()|0);return new r.init(c,a)}}),w=d.enc={},v=w.Hex={stringify:function(a){var c=a.words;a=a.sigBytes;for(var e=[],j=0;j<a;j++){var k=c[j>>>2]>>>24-8*(j%4)&255;e.push((k>>>4).toString(16));e.push((k&15).toString(16))}return e.join("")},parse:function(a){for(var c=a.length,e=[],j=0;j<c;j+=2)e[j>>>3]|=parseInt(a.substr(j,
2),16)<<24-4*(j%8);return new r.init(e,c/2)}},b=w.Latin1={stringify:function(a){var c=a.words;a=a.sigBytes;for(var e=[],j=0;j<a;j++)e.push(String.fromCharCode(c[j>>>2]>>>24-8*(j%4)&255));return e.join("")},parse:function(a){for(var c=a.length,e=[],j=0;j<c;j++)e[j>>>2]|=(a.charCodeAt(j)&255)<<24-8*(j%4);return new r.init(e,c)}},x=w.Utf8={stringify:function(a){try{return decodeURIComponent(escape(b.stringify(a)))}catch(c){throw Error("Malformed UTF-8 data");}},parse:function(a){return b.parse(unescape(encodeURIComponent(a)))}},
q=l.BufferedBlockAlgorithm=t.extend({reset:function(){this._data=new r.init;this._nDataBytes=0},_append:function(a){"string"==typeof a&&(a=x.parse(a));this._data.concat(a);this._nDataBytes+=a.sigBytes},_process:function(a){var c=this._data,e=c.words,j=c.sigBytes,k=this.blockSize,b=j/(4*k),b=a?u.ceil(b):u.max((b|0)-this._minBufferSize,0);a=b*k;j=u.min(4*a,j);if(a){for(var q=0;q<a;q+=k)this._doProcessBlock(e,q);q=e.splice(0,a);c.sigBytes-=j}return new r.init(q,j)},clone:function(){var a=t.clone.call(this);
a._data=this._data.clone();return a},_minBufferSize:0});l.Hasher=q.extend({cfg:t.extend(),init:function(a){this.cfg=this.cfg.extend(a);this.reset()},reset:function(){q.reset.call(this);this._doReset()},update:function(a){this._append(a);this._process();return this},finalize:function(a){a&&this._append(a);return this._doFinalize()},blockSize:16,_createHelper:function(a){return function(b,e){return(new a.init(e)).finalize(b)}},_createHmacHelper:function(a){return function(b,e){return(new n.HMAC.init(a,
e)).finalize(b)}}});var n=d.algo={};return d}(Math);
(function(){var u=CryptoJS,p=u.lib.WordArray;u.enc.Base64={stringify:function(d){var l=d.words,p=d.sigBytes,t=this._map;d.clamp();d=[];for(var r=0;r<p;r+=3)for(var w=(l[r>>>2]>>>24-8*(r%4)&255)<<16|(l[r+1>>>2]>>>24-8*((r+1)%4)&255)<<8|l[r+2>>>2]>>>24-8*((r+2)%4)&255,v=0;4>v&&r+0.75*v<p;v++)d.push(t.charAt(w>>>6*(3-v)&63));if(l=t.charAt(64))for(;d.length%4;)d.push(l);return d.join("")},parse:function(d){var l=d.length,s=this._map,t=s.charAt(64);t&&(t=d.indexOf(t),-1!=t&&(l=t));for(var t=[],r=0,w=0;w<
l;w++)if(w%4){var v=s.indexOf(d.charAt(w-1))<<2*(w%4),b=s.indexOf(d.charAt(w))>>>6-2*(w%4);t[r>>>2]|=(v|b)<<24-8*(r%4);r++}return p.create(t,r)},_map:"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/="}})();
(function(u){function p(b,n,a,c,e,j,k){b=b+(n&a|~n&c)+e+k;return(b<<j|b>>>32-j)+n}function d(b,n,a,c,e,j,k){b=b+(n&c|a&~c)+e+k;return(b<<j|b>>>32-j)+n}function l(b,n,a,c,e,j,k){b=b+(n^a^c)+e+k;return(b<<j|b>>>32-j)+n}function s(b,n,a,c,e,j,k){b=b+(a^(n|~c))+e+k;return(b<<j|b>>>32-j)+n}for(var t=CryptoJS,r=t.lib,w=r.WordArray,v=r.Hasher,r=t.algo,b=[],x=0;64>x;x++)b[x]=4294967296*u.abs(u.sin(x+1))|0;r=r.MD5=v.extend({_doReset:function(){this._hash=new w.init([1732584193,4023233417,2562383102,271733878])},
_doProcessBlock:function(q,n){for(var a=0;16>a;a++){var c=n+a,e=q[c];q[c]=(e<<8|e>>>24)&16711935|(e<<24|e>>>8)&4278255360}var a=this._hash.words,c=q[n+0],e=q[n+1],j=q[n+2],k=q[n+3],z=q[n+4],r=q[n+5],t=q[n+6],w=q[n+7],v=q[n+8],A=q[n+9],B=q[n+10],C=q[n+11],u=q[n+12],D=q[n+13],E=q[n+14],x=q[n+15],f=a[0],m=a[1],g=a[2],h=a[3],f=p(f,m,g,h,c,7,b[0]),h=p(h,f,m,g,e,12,b[1]),g=p(g,h,f,m,j,17,b[2]),m=p(m,g,h,f,k,22,b[3]),f=p(f,m,g,h,z,7,b[4]),h=p(h,f,m,g,r,12,b[5]),g=p(g,h,f,m,t,17,b[6]),m=p(m,g,h,f,w,22,b[7]),
f=p(f,m,g,h,v,7,b[8]),h=p(h,f,m,g,A,12,b[9]),g=p(g,h,f,m,B,17,b[10]),m=p(m,g,h,f,C,22,b[11]),f=p(f,m,g,h,u,7,b[12]),h=p(h,f,m,g,D,12,b[13]),g=p(g,h,f,m,E,17,b[14]),m=p(m,g,h,f,x,22,b[15]),f=d(f,m,g,h,e,5,b[16]),h=d(h,f,m,g,t,9,b[17]),g=d(g,h,f,m,C,14,b[18]),m=d(m,g,h,f,c,20,b[19]),f=d(f,m,g,h,r,5,b[20]),h=d(h,f,m,g,B,9,b[21]),g=d(g,h,f,m,x,14,b[22]),m=d(m,g,h,f,z,20,b[23]),f=d(f,m,g,h,A,5,b[24]),h=d(h,f,m,g,E,9,b[25]),g=d(g,h,f,m,k,14,b[26]),m=d(m,g,h,f,v,20,b[27]),f=d(f,m,g,h,D,5,b[28]),h=d(h,f,
m,g,j,9,b[29]),g=d(g,h,f,m,w,14,b[30]),m=d(m,g,h,f,u,20,b[31]),f=l(f,m,g,h,r,4,b[32]),h=l(h,f,m,g,v,11,b[33]),g=l(g,h,f,m,C,16,b[34]),m=l(m,g,h,f,E,23,b[35]),f=l(f,m,g,h,e,4,b[36]),h=l(h,f,m,g,z,11,b[37]),g=l(g,h,f,m,w,16,b[38]),m=l(m,g,h,f,B,23,b[39]),f=l(f,m,g,h,D,4,b[40]),h=l(h,f,m,g,c,11,b[41]),g=l(g,h,f,m,k,16,b[42]),m=l(m,g,h,f,t,23,b[43]),f=l(f,m,g,h,A,4,b[44]),h=l(h,f,m,g,u,11,b[45]),g=l(g,h,f,m,x,16,b[46]),m=l(m,g,h,f,j,23,b[47]),f=s(f,m,g,h,c,6,b[48]),h=s(h,f,m,g,w,10,b[49]),g=s(g,h,f,m,
E,15,b[50]),m=s(m,g,h,f,r,21,b[51]),f=s(f,m,g,h,u,6,b[52]),h=s(h,f,m,g,k,10,b[53]),g=s(g,h,f,m,B,15,b[54]),m=s(m,g,h,f,e,21,b[55]),f=s(f,m,g,h,v,6,b[56]),h=s(h,f,m,g,x,10,b[57]),g=s(g,h,f,m,t,15,b[58]),m=s(m,g,h,f,D,21,b[59]),f=s(f,m,g,h,z,6,b[60]),h=s(h,f,m,g,C,10,b[61]),g=s(g,h,f,m,j,15,b[62]),m=s(m,g,h,f,A,21,b[63]);a[0]=a[0]+f|0;a[1]=a[1]+m|0;a[2]=a[2]+g|0;a[3]=a[3]+h|0},_doFinalize:function(){var b=this._data,n=b.words,a=8*this._nDataBytes,c=8*b.sigBytes;n[c>>>5]|=128<<24-c%32;var e=u.floor(a/
4294967296);n[(c+64>>>9<<4)+15]=(e<<8|e>>>24)&16711935|(e<<24|e>>>8)&4278255360;n[(c+64>>>9<<4)+14]=(a<<8|a>>>24)&16711935|(a<<24|a>>>8)&4278255360;b.sigBytes=4*(n.length+1);this._process();b=this._hash;n=b.words;for(a=0;4>a;a++)c=n[a],n[a]=(c<<8|c>>>24)&16711935|(c<<24|c>>>8)&4278255360;return b},clone:function(){var b=v.clone.call(this);b._hash=this._hash.clone();return b}});t.MD5=v._createHelper(r);t.HmacMD5=v._createHmacHelper(r)})(Math);
(function(){var u=CryptoJS,p=u.lib,d=p.Base,l=p.WordArray,p=u.algo,s=p.EvpKDF=d.extend({cfg:d.extend({keySize:4,hasher:p.MD5,iterations:1}),init:function(d){this.cfg=this.cfg.extend(d)},compute:function(d,r){for(var p=this.cfg,s=p.hasher.create(),b=l.create(),u=b.words,q=p.keySize,p=p.iterations;u.length<q;){n&&s.update(n);var n=s.update(d).finalize(r);s.reset();for(var a=1;a<p;a++)n=s.finalize(n),s.reset();b.concat(n)}b.sigBytes=4*q;return b}});u.EvpKDF=function(d,l,p){return s.create(p).compute(d,
l)}})();
CryptoJS.lib.Cipher||function(u){var p=CryptoJS,d=p.lib,l=d.Base,s=d.WordArray,t=d.BufferedBlockAlgorithm,r=p.enc.Base64,w=p.algo.EvpKDF,v=d.Cipher=t.extend({cfg:l.extend(),createEncryptor:function(e,a){return this.create(this._ENC_XFORM_MODE,e,a)},createDecryptor:function(e,a){return this.create(this._DEC_XFORM_MODE,e,a)},init:function(e,a,b){this.cfg=this.cfg.extend(b);this._xformMode=e;this._key=a;this.reset()},reset:function(){t.reset.call(this);this._doReset()},process:function(e){this._append(e);return this._process()},
finalize:function(e){e&&this._append(e);return this._doFinalize()},keySize:4,ivSize:4,_ENC_XFORM_MODE:1,_DEC_XFORM_MODE:2,_createHelper:function(e){return{encrypt:function(b,k,d){return("string"==typeof k?c:a).encrypt(e,b,k,d)},decrypt:function(b,k,d){return("string"==typeof k?c:a).decrypt(e,b,k,d)}}}});d.StreamCipher=v.extend({_doFinalize:function(){return this._process(!0)},blockSize:1});var b=p.mode={},x=function(e,a,b){var c=this._iv;c?this._iv=u:c=this._prevBlock;for(var d=0;d<b;d++)e[a+d]^=
c[d]},q=(d.BlockCipherMode=l.extend({createEncryptor:function(e,a){return this.Encryptor.create(e,a)},createDecryptor:function(e,a){return this.Decryptor.create(e,a)},init:function(e,a){this._cipher=e;this._iv=a}})).extend();q.Encryptor=q.extend({processBlock:function(e,a){var b=this._cipher,c=b.blockSize;x.call(this,e,a,c);b.encryptBlock(e,a);this._prevBlock=e.slice(a,a+c)}});q.Decryptor=q.extend({processBlock:function(e,a){var b=this._cipher,c=b.blockSize,d=e.slice(a,a+c);b.decryptBlock(e,a);x.call(this,
e,a,c);this._prevBlock=d}});b=b.CBC=q;q=(p.pad={}).Pkcs7={pad:function(a,b){for(var c=4*b,c=c-a.sigBytes%c,d=c<<24|c<<16|c<<8|c,l=[],n=0;n<c;n+=4)l.push(d);c=s.create(l,c);a.concat(c)},unpad:function(a){a.sigBytes-=a.words[a.sigBytes-1>>>2]&255}};d.BlockCipher=v.extend({cfg:v.cfg.extend({mode:b,padding:q}),reset:function(){v.reset.call(this);var a=this.cfg,b=a.iv,a=a.mode;if(this._xformMode==this._ENC_XFORM_MODE)var c=a.createEncryptor;else c=a.createDecryptor,this._minBufferSize=1;this._mode=c.call(a,
this,b&&b.words)},_doProcessBlock:function(a,b){this._mode.processBlock(a,b)},_doFinalize:function(){var a=this.cfg.padding;if(this._xformMode==this._ENC_XFORM_MODE){a.pad(this._data,this.blockSize);var b=this._process(!0)}else b=this._process(!0),a.unpad(b);return b},blockSize:4});var n=d.CipherParams=l.extend({init:function(a){this.mixIn(a)},toString:function(a){return(a||this.formatter).stringify(this)}}),b=(p.format={}).OpenSSL={stringify:function(a){var b=a.ciphertext;a=a.salt;return(a?s.create([1398893684,
1701076831]).concat(a).concat(b):b).toString(r)},parse:function(a){a=r.parse(a);var b=a.words;if(1398893684==b[0]&&1701076831==b[1]){var c=s.create(b.slice(2,4));b.splice(0,4);a.sigBytes-=16}return n.create({ciphertext:a,salt:c})}},a=d.SerializableCipher=l.extend({cfg:l.extend({format:b}),encrypt:function(a,b,c,d){d=this.cfg.extend(d);var l=a.createEncryptor(c,d);b=l.finalize(b);l=l.cfg;return n.create({ciphertext:b,key:c,iv:l.iv,algorithm:a,mode:l.mode,padding:l.padding,blockSize:a.blockSize,formatter:d.format})},
decrypt:function(a,b,c,d){d=this.cfg.extend(d);b=this._parse(b,d.format);return a.createDecryptor(c,d).finalize(b.ciphertext)},_parse:function(a,b){return"string"==typeof a?b.parse(a,this):a}}),p=(p.kdf={}).OpenSSL={execute:function(a,b,c,d){d||(d=s.random(8));a=w.create({keySize:b+c}).compute(a,d);c=s.create(a.words.slice(b),4*c);a.sigBytes=4*b;return n.create({key:a,iv:c,salt:d})}},c=d.PasswordBasedCipher=a.extend({cfg:a.cfg.extend({kdf:p}),encrypt:function(b,c,d,l){l=this.cfg.extend(l);d=l.kdf.execute(d,
b.keySize,b.ivSize);l.iv=d.iv;b=a.encrypt.call(this,b,c,d.key,l);b.mixIn(d);return b},decrypt:function(b,c,d,l){l=this.cfg.extend(l);c=this._parse(c,l.format);d=l.kdf.execute(d,b.keySize,b.ivSize,c.salt);l.iv=d.iv;return a.decrypt.call(this,b,c,d.key,l)}})}();
(function(){for(var u=CryptoJS,p=u.lib.BlockCipher,d=u.algo,l=[],s=[],t=[],r=[],w=[],v=[],b=[],x=[],q=[],n=[],a=[],c=0;256>c;c++)a[c]=128>c?c<<1:c<<1^283;for(var e=0,j=0,c=0;256>c;c++){var k=j^j<<1^j<<2^j<<3^j<<4,k=k>>>8^k&255^99;l[e]=k;s[k]=e;var z=a[e],F=a[z],G=a[F],y=257*a[k]^16843008*k;t[e]=y<<24|y>>>8;r[e]=y<<16|y>>>16;w[e]=y<<8|y>>>24;v[e]=y;y=16843009*G^65537*F^257*z^16843008*e;b[k]=y<<24|y>>>8;x[k]=y<<16|y>>>16;q[k]=y<<8|y>>>24;n[k]=y;e?(e=z^a[a[a[G^z]]],j^=a[a[j]]):e=j=1}var H=[0,1,2,4,8,
16,32,64,128,27,54],d=d.AES=p.extend({_doReset:function(){for(var a=this._key,c=a.words,d=a.sigBytes/4,a=4*((this._nRounds=d+6)+1),e=this._keySchedule=[],j=0;j<a;j++)if(j<d)e[j]=c[j];else{var k=e[j-1];j%d?6<d&&4==j%d&&(k=l[k>>>24]<<24|l[k>>>16&255]<<16|l[k>>>8&255]<<8|l[k&255]):(k=k<<8|k>>>24,k=l[k>>>24]<<24|l[k>>>16&255]<<16|l[k>>>8&255]<<8|l[k&255],k^=H[j/d|0]<<24);e[j]=e[j-d]^k}c=this._invKeySchedule=[];for(d=0;d<a;d++)j=a-d,k=d%4?e[j]:e[j-4],c[d]=4>d||4>=j?k:b[l[k>>>24]]^x[l[k>>>16&255]]^q[l[k>>>
8&255]]^n[l[k&255]]},encryptBlock:function(a,b){this._doCryptBlock(a,b,this._keySchedule,t,r,w,v,l)},decryptBlock:function(a,c){var d=a[c+1];a[c+1]=a[c+3];a[c+3]=d;this._doCryptBlock(a,c,this._invKeySchedule,b,x,q,n,s);d=a[c+1];a[c+1]=a[c+3];a[c+3]=d},_doCryptBlock:function(a,b,c,d,e,j,l,f){for(var m=this._nRounds,g=a[b]^c[0],h=a[b+1]^c[1],k=a[b+2]^c[2],n=a[b+3]^c[3],p=4,r=1;r<m;r++)var q=d[g>>>24]^e[h>>>16&255]^j[k>>>8&255]^l[n&255]^c[p++],s=d[h>>>24]^e[k>>>16&255]^j[n>>>8&255]^l[g&255]^c[p++],t=
d[k>>>24]^e[n>>>16&255]^j[g>>>8&255]^l[h&255]^c[p++],n=d[n>>>24]^e[g>>>16&255]^j[h>>>8&255]^l[k&255]^c[p++],g=q,h=s,k=t;q=(f[g>>>24]<<24|f[h>>>16&255]<<16|f[k>>>8&255]<<8|f[n&255])^c[p++];s=(f[h>>>24]<<24|f[k>>>16&255]<<16|f[n>>>8&255]<<8|f[g&255])^c[p++];t=(f[k>>>24]<<24|f[n>>>16&255]<<16|f[g>>>8&255]<<8|f[h&255])^c[p++];n=(f[n>>>24]<<24|f[g>>>16&255]<<16|f[h>>>8&255]<<8|f[k&255])^c[p++];a[b]=q;a[b+1]=s;a[b+2]=t;a[b+3]=n},keySize:8});u.AES=p._createHelper(d)})();
 //next 


//start 

 // Copyright (c) 2005  Tom Wu
// All Rights Reserved.
// See "LICENSE" for details.

// Basic JavaScript BN library - subset useful for RSA encryption.

// Bits per digit
var dbits;

// JavaScript engine analysis
var canary = 0xdeadbeefcafe;
var j_lm = ((canary&0xffffff)==0xefcafe);

// (public) Constructor
function BigInteger(a,b,c) {
  if (!(this instanceof BigInteger)) {
    return new BigInteger(a, b, c);
  }

  if(a != null) {
    if("number" == typeof a) this.fromNumber(a,b,c);
    else if(b == null && "string" != typeof a) this.fromString(a,256);
    else this.fromString(a,b);
  }
}

var proto = BigInteger.prototype;

// return new, unset BigInteger
function nbi() { return new BigInteger(null); }

// am: Compute w_j += (x*this_i), propagate carries,
// c is initial carry, returns final carry.
// c < 3*dvalue, x < 2*dvalue, this_i < dvalue
// We need to select the fastest one that works in this environment.

// am1: use a single mult and divide to get the high bits,
// max digit bits should be 26 because
// max internal value = 2*dvalue^2-2*dvalue (< 2^53)
function am1(i,x,w,j,c,n) {
  while(--n >= 0) {
    var v = x*this[i++]+w[j]+c;
    c = Math.floor(v/0x4000000);
    w[j++] = v&0x3ffffff;
  }
  return c;
}
// am2 avoids a big mult-and-extract completely.
// Max digit bits should be <= 30 because we do bitwise ops
// on values up to 2*hdvalue^2-hdvalue-1 (< 2^31)
function am2(i,x,w,j,c,n) {
  var xl = x&0x7fff, xh = x>>15;
  while(--n >= 0) {
    var l = this[i]&0x7fff;
    var h = this[i++]>>15;
    var m = xh*l+h*xl;
    l = xl*l+((m&0x7fff)<<15)+w[j]+(c&0x3fffffff);
    c = (l>>>30)+(m>>>15)+xh*h+(c>>>30);
    w[j++] = l&0x3fffffff;
  }
  return c;
}
// Alternately, set max digit bits to 28 since some
// browsers slow down when dealing with 32-bit numbers.
function am3(i,x,w,j,c,n) {
  var xl = x&0x3fff, xh = x>>14;
  while(--n >= 0) {
    var l = this[i]&0x3fff;
    var h = this[i++]>>14;
    var m = xh*l+h*xl;
    l = xl*l+((m&0x3fff)<<14)+w[j]+c;
    c = (l>>28)+(m>>14)+xh*h;
    w[j++] = l&0xfffffff;
  }
  return c;
}

// wtf?
BigInteger.prototype.am = am1;
dbits = 26;

/*
if(j_lm && (navigator.appName == "Microsoft Internet Explorer")) {
  BigInteger.prototype.am = am2;
  dbits = 30;
}
else if(j_lm && (navigator.appName != "Netscape")) {
  BigInteger.prototype.am = am1;
  dbits = 26;
}
else { // Mozilla/Netscape seems to prefer am3
  BigInteger.prototype.am = am3;
  dbits = 28;
}
*/

BigInteger.prototype.DB = dbits;
BigInteger.prototype.DM = ((1<<dbits)-1);
var DV = BigInteger.prototype.DV = (1<<dbits);

var BI_FP = 52;
BigInteger.prototype.FV = Math.pow(2,BI_FP);
BigInteger.prototype.F1 = BI_FP-dbits;
BigInteger.prototype.F2 = 2*dbits-BI_FP;

// Digit conversions
var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
var BI_RC = new Array();
var rr,vv;
rr = "0".charCodeAt(0);
for(vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
rr = "a".charCodeAt(0);
for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
rr = "A".charCodeAt(0);
for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;

function int2char(n) { return BI_RM.charAt(n); }
function intAt(s,i) {
  var c = BI_RC[s.charCodeAt(i)];
  return (c==null)?-1:c;
}

// (protected) copy this to r
function bnpCopyTo(r) {
  for(var i = this.t-1; i >= 0; --i) r[i] = this[i];
  r.t = this.t;
  r.s = this.s;
}

// (protected) set from integer value x, -DV <= x < DV
function bnpFromInt(x) {
  this.t = 1;
  this.s = (x<0)?-1:0;
  if(x > 0) this[0] = x;
  else if(x < -1) this[0] = x+DV;
  else this.t = 0;
}

// return bigint initialized to value
function nbv(i) { var r = nbi(); r.fromInt(i); return r; }

// (protected) set from string and radix
function bnpFromString(s,b) {
  var self = this;

  var k;
  if(b == 16) k = 4;
  else if(b == 8) k = 3;
  else if(b == 256) k = 8; // byte array
  else if(b == 2) k = 1;
  else if(b == 32) k = 5;
  else if(b == 4) k = 2;
  else { self.fromRadix(s,b); return; }
  self.t = 0;
  self.s = 0;
  var i = s.length, mi = false, sh = 0;
  while(--i >= 0) {
    var x = (k==8)?s[i]&0xff:intAt(s,i);
    if(x < 0) {
      if(s.charAt(i) == "-") mi = true;
      continue;
    }
    mi = false;
    if(sh == 0)
      self[self.t++] = x;
    else if(sh+k > self.DB) {
      self[self.t-1] |= (x&((1<<(self.DB-sh))-1))<<sh;
      self[self.t++] = (x>>(self.DB-sh));
    }
    else
      self[self.t-1] |= x<<sh;
    sh += k;
    if(sh >= self.DB) sh -= self.DB;
  }
  if(k == 8 && (s[0]&0x80) != 0) {
    self.s = -1;
    if(sh > 0) self[self.t-1] |= ((1<<(self.DB-sh))-1)<<sh;
  }
  self.clamp();
  if(mi) BigInteger.ZERO.subTo(self,self);
}

// (protected) clamp off excess high words
function bnpClamp() {
  var c = this.s&this.DM;
  while(this.t > 0 && this[this.t-1] == c) --this.t;
}

// (public) return string representation in given radix
function bnToString(b) {
  var self = this;
  if(self.s < 0) return "-"+self.negate().toString(b);
  var k;
  if(b == 16) k = 4;
  else if(b == 8) k = 3;
  else if(b == 2) k = 1;
  else if(b == 32) k = 5;
  else if(b == 4) k = 2;
  else return self.toRadix(b);
  var km = (1<<k)-1, d, m = false, r = "", i = self.t;
  var p = self.DB-(i*self.DB)%k;
  if(i-- > 0) {
    if(p < self.DB && (d = self[i]>>p) > 0) { m = true; r = int2char(d); }
    while(i >= 0) {
      if(p < k) {
        d = (self[i]&((1<<p)-1))<<(k-p);
        d |= self[--i]>>(p+=self.DB-k);
      }
      else {
        d = (self[i]>>(p-=k))&km;
        if(p <= 0) { p += self.DB; --i; }
      }
      if(d > 0) m = true;
      if(m) r += int2char(d);
    }
  }
  return m?r:"0";
}

// (public) -this
function bnNegate() { var r = nbi(); BigInteger.ZERO.subTo(this,r); return r; }

// (public) |this|
function bnAbs() { return (this.s<0)?this.negate():this; }

// (public) return + if this > a, - if this < a, 0 if equal
function bnCompareTo(a) {
  var r = this.s-a.s;
  if(r != 0) return r;
  var i = this.t;
  r = i-a.t;
  if(r != 0) return (this.s<0)?-r:r;
  while(--i >= 0) if((r=this[i]-a[i]) != 0) return r;
  return 0;
}

// returns bit length of the integer x
function nbits(x) {
  var r = 1, t;
  if((t=x>>>16) != 0) { x = t; r += 16; }
  if((t=x>>8) != 0) { x = t; r += 8; }
  if((t=x>>4) != 0) { x = t; r += 4; }
  if((t=x>>2) != 0) { x = t; r += 2; }
  if((t=x>>1) != 0) { x = t; r += 1; }
  return r;
}

// (public) return the number of bits in "this"
function bnBitLength() {
  if(this.t <= 0) return 0;
  return this.DB*(this.t-1)+nbits(this[this.t-1]^(this.s&this.DM));
}

// (protected) r = this << n*DB
function bnpDLShiftTo(n,r) {
  var i;
  for(i = this.t-1; i >= 0; --i) r[i+n] = this[i];
  for(i = n-1; i >= 0; --i) r[i] = 0;
  r.t = this.t+n;
  r.s = this.s;
}

// (protected) r = this >> n*DB
function bnpDRShiftTo(n,r) {
  for(var i = n; i < this.t; ++i) r[i-n] = this[i];
  r.t = Math.max(this.t-n,0);
  r.s = this.s;
}

// (protected) r = this << n
function bnpLShiftTo(n,r) {
  var self = this;
  var bs = n%self.DB;
  var cbs = self.DB-bs;
  var bm = (1<<cbs)-1;
  var ds = Math.floor(n/self.DB), c = (self.s<<bs)&self.DM, i;
  for(i = self.t-1; i >= 0; --i) {
    r[i+ds+1] = (self[i]>>cbs)|c;
    c = (self[i]&bm)<<bs;
  }
  for(i = ds-1; i >= 0; --i) r[i] = 0;
  r[ds] = c;
  r.t = self.t+ds+1;
  r.s = self.s;
  r.clamp();
}

// (protected) r = this >> n
function bnpRShiftTo(n,r) {
  var self = this;
  r.s = self.s;
  var ds = Math.floor(n/self.DB);
  if(ds >= self.t) { r.t = 0; return; }
  var bs = n%self.DB;
  var cbs = self.DB-bs;
  var bm = (1<<bs)-1;
  r[0] = self[ds]>>bs;
  for(var i = ds+1; i < self.t; ++i) {
    r[i-ds-1] |= (self[i]&bm)<<cbs;
    r[i-ds] = self[i]>>bs;
  }
  if(bs > 0) r[self.t-ds-1] |= (self.s&bm)<<cbs;
  r.t = self.t-ds;
  r.clamp();
}

// (protected) r = this - a
function bnpSubTo(a,r) {
  var self = this;
  var i = 0, c = 0, m = Math.min(a.t,self.t);
  while(i < m) {
    c += self[i]-a[i];
    r[i++] = c&self.DM;
    c >>= self.DB;
  }
  if(a.t < self.t) {
    c -= a.s;
    while(i < self.t) {
      c += self[i];
      r[i++] = c&self.DM;
      c >>= self.DB;
    }
    c += self.s;
  }
  else {
    c += self.s;
    while(i < a.t) {
      c -= a[i];
      r[i++] = c&self.DM;
      c >>= self.DB;
    }
    c -= a.s;
  }
  r.s = (c<0)?-1:0;
  if(c < -1) r[i++] = self.DV+c;
  else if(c > 0) r[i++] = c;
  r.t = i;
  r.clamp();
}

// (protected) r = this * a, r != this,a (HAC 14.12)
// "this" should be the larger one if appropriate.
function bnpMultiplyTo(a,r) {
  var x = this.abs(), y = a.abs();
  var i = x.t;
  r.t = i+y.t;
  while(--i >= 0) r[i] = 0;
  for(i = 0; i < y.t; ++i) r[i+x.t] = x.am(0,y[i],r,i,0,x.t);
  r.s = 0;
  r.clamp();
  if(this.s != a.s) BigInteger.ZERO.subTo(r,r);
}

// (protected) r = this^2, r != this (HAC 14.16)
function bnpSquareTo(r) {
  var x = this.abs();
  var i = r.t = 2*x.t;
  while(--i >= 0) r[i] = 0;
  for(i = 0; i < x.t-1; ++i) {
    var c = x.am(i,x[i],r,2*i,0,1);
    if((r[i+x.t]+=x.am(i+1,2*x[i],r,2*i+1,c,x.t-i-1)) >= x.DV) {
      r[i+x.t] -= x.DV;
      r[i+x.t+1] = 1;
    }
  }
  if(r.t > 0) r[r.t-1] += x.am(i,x[i],r,2*i,0,1);
  r.s = 0;
  r.clamp();
}

// (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
// r != q, this != m.  q or r may be null.
function bnpDivRemTo(m,q,r) {
  var self = this;
  var pm = m.abs();
  if(pm.t <= 0) return;
  var pt = self.abs();
  if(pt.t < pm.t) {
    if(q != null) q.fromInt(0);
    if(r != null) self.copyTo(r);
    return;
  }
  if(r == null) r = nbi();
  var y = nbi(), ts = self.s, ms = m.s;
  var nsh = self.DB-nbits(pm[pm.t-1]);	// normalize modulus
  if(nsh > 0) { pm.lShiftTo(nsh,y); pt.lShiftTo(nsh,r); }
  else { pm.copyTo(y); pt.copyTo(r); }
  var ys = y.t;
  var y0 = y[ys-1];
  if(y0 == 0) return;
  var yt = y0*(1<<self.F1)+((ys>1)?y[ys-2]>>self.F2:0);
  var d1 = self.FV/yt, d2 = (1<<self.F1)/yt, e = 1<<self.F2;
  var i = r.t, j = i-ys, t = (q==null)?nbi():q;
  y.dlShiftTo(j,t);
  if(r.compareTo(t) >= 0) {
    r[r.t++] = 1;
    r.subTo(t,r);
  }
  BigInteger.ONE.dlShiftTo(ys,t);
  t.subTo(y,y);	// "negative" y so we can replace sub with am later
  while(y.t < ys) y[y.t++] = 0;
  while(--j >= 0) {
    // Estimate quotient digit
    var qd = (r[--i]==y0)?self.DM:Math.floor(r[i]*d1+(r[i-1]+e)*d2);
    if((r[i]+=y.am(0,qd,r,j,0,ys)) < qd) {	// Try it out
      y.dlShiftTo(j,t);
      r.subTo(t,r);
      while(r[i] < --qd) r.subTo(t,r);
    }
  }
  if(q != null) {
    r.drShiftTo(ys,q);
    if(ts != ms) BigInteger.ZERO.subTo(q,q);
  }
  r.t = ys;
  r.clamp();
  if(nsh > 0) r.rShiftTo(nsh,r);	// Denormalize remainder
  if(ts < 0) BigInteger.ZERO.subTo(r,r);
}

// (public) this mod a
function bnMod(a) {
  var r = nbi();
  this.abs().divRemTo(a,null,r);
  if(this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r,r);
  return r;
}

// Modular reduction using "classic" algorithm
function Classic(m) { this.m = m; }
function cConvert(x) {
  if(x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
  else return x;
}
function cRevert(x) { return x; }
function cReduce(x) { x.divRemTo(this.m,null,x); }
function cMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }
function cSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

Classic.prototype.convert = cConvert;
Classic.prototype.revert = cRevert;
Classic.prototype.reduce = cReduce;
Classic.prototype.mulTo = cMulTo;
Classic.prototype.sqrTo = cSqrTo;

// (protected) return "-1/this % 2^DB"; useful for Mont. reduction
// justification:
//         xy == 1 (mod m)
//         xy =  1+km
//   xy(2-xy) = (1+km)(1-km)
// x[y(2-xy)] = 1-k^2m^2
// x[y(2-xy)] == 1 (mod m^2)
// if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
// should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
// JS multiply "overflows" differently from C/C++, so care is needed here.
function bnpInvDigit() {
  if(this.t < 1) return 0;
  var x = this[0];
  if((x&1) == 0) return 0;
  var y = x&3;		// y == 1/x mod 2^2
  y = (y*(2-(x&0xf)*y))&0xf;	// y == 1/x mod 2^4
  y = (y*(2-(x&0xff)*y))&0xff;	// y == 1/x mod 2^8
  y = (y*(2-(((x&0xffff)*y)&0xffff)))&0xffff;	// y == 1/x mod 2^16
  // last step - calculate inverse mod DV directly;
  // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
  y = (y*(2-x*y%this.DV))%this.DV;		// y == 1/x mod 2^dbits
  // we really want the negative inverse, and -DV < y < DV
  return (y>0)?this.DV-y:-y;
}

// Montgomery reduction
function Montgomery(m) {
  this.m = m;
  this.mp = m.invDigit();
  this.mpl = this.mp&0x7fff;
  this.mph = this.mp>>15;
  this.um = (1<<(m.DB-15))-1;
  this.mt2 = 2*m.t;
}

// xR mod m
function montConvert(x) {
  var r = nbi();
  x.abs().dlShiftTo(this.m.t,r);
  r.divRemTo(this.m,null,r);
  if(x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r,r);
  return r;
}

// x/R mod m
function montRevert(x) {
  var r = nbi();
  x.copyTo(r);
  this.reduce(r);
  return r;
}

// x = x/R mod m (HAC 14.32)
function montReduce(x) {
  while(x.t <= this.mt2)	// pad x so am has enough room later
    x[x.t++] = 0;
  for(var i = 0; i < this.m.t; ++i) {
    // faster way of calculating u0 = x[i]*mp mod DV
    var j = x[i]&0x7fff;
    var u0 = (j*this.mpl+(((j*this.mph+(x[i]>>15)*this.mpl)&this.um)<<15))&x.DM;
    // use am to combine the multiply-shift-add into one call
    j = i+this.m.t;
    x[j] += this.m.am(0,u0,x,i,0,this.m.t);
    // propagate carry
    while(x[j] >= x.DV) { x[j] -= x.DV; x[++j]++; }
  }
  x.clamp();
  x.drShiftTo(this.m.t,x);
  if(x.compareTo(this.m) >= 0) x.subTo(this.m,x);
}

// r = "x^2/R mod m"; x != r
function montSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

// r = "xy/R mod m"; x,y != r
function montMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }

Montgomery.prototype.convert = montConvert;
Montgomery.prototype.revert = montRevert;
Montgomery.prototype.reduce = montReduce;
Montgomery.prototype.mulTo = montMulTo;
Montgomery.prototype.sqrTo = montSqrTo;

// (protected) true iff this is even
function bnpIsEven() { return ((this.t>0)?(this[0]&1):this.s) == 0; }

// (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)
function bnpExp(e,z) {
  if(e > 0xffffffff || e < 1) return BigInteger.ONE;
  var r = nbi(), r2 = nbi(), g = z.convert(this), i = nbits(e)-1;
  g.copyTo(r);
  while(--i >= 0) {
    z.sqrTo(r,r2);
    if((e&(1<<i)) > 0) z.mulTo(r2,g,r);
    else { var t = r; r = r2; r2 = t; }
  }
  return z.revert(r);
}

// (public) this^e % m, 0 <= e < 2^32
function bnModPowInt(e,m) {
  var z;
  if(e < 256 || m.isEven()) z = new Classic(m); else z = new Montgomery(m);
  return this.exp(e,z);
}

// protected
proto.copyTo = bnpCopyTo;
proto.fromInt = bnpFromInt;
proto.fromString = bnpFromString;
proto.clamp = bnpClamp;
proto.dlShiftTo = bnpDLShiftTo;
proto.drShiftTo = bnpDRShiftTo;
proto.lShiftTo = bnpLShiftTo;
proto.rShiftTo = bnpRShiftTo;
proto.subTo = bnpSubTo;
proto.multiplyTo = bnpMultiplyTo;
proto.squareTo = bnpSquareTo;
proto.divRemTo = bnpDivRemTo;
proto.invDigit = bnpInvDigit;
proto.isEven = bnpIsEven;
proto.exp = bnpExp;

// public
proto.toString = bnToString;
proto.negate = bnNegate;
proto.abs = bnAbs;
proto.compareTo = bnCompareTo;
proto.bitLength = bnBitLength;
proto.mod = bnMod;
proto.modPowInt = bnModPowInt;

//// jsbn2

function nbi() { return new BigInteger(null); }

// (public)
function bnClone() { var r = nbi(); this.copyTo(r); return r; }

// (public) return value as integer
function bnIntValue() {
  if(this.s < 0) {
    if(this.t == 1) return this[0]-this.DV;
    else if(this.t == 0) return -1;
  }
  else if(this.t == 1) return this[0];
  else if(this.t == 0) return 0;
  // assumes 16 < DB < 32
  return ((this[1]&((1<<(32-this.DB))-1))<<this.DB)|this[0];
}

// (public) return value as byte
function bnByteValue() { return (this.t==0)?this.s:(this[0]<<24)>>24; }

// (public) return value as short (assumes DB>=16)
function bnShortValue() { return (this.t==0)?this.s:(this[0]<<16)>>16; }

// (protected) return x s.t. r^x < DV
function bnpChunkSize(r) { return Math.floor(Math.LN2*this.DB/Math.log(r)); }

// (public) 0 if this == 0, 1 if this > 0
function bnSigNum() {
  if(this.s < 0) return -1;
  else if(this.t <= 0 || (this.t == 1 && this[0] <= 0)) return 0;
  else return 1;
}

// (protected) convert to radix string
function bnpToRadix(b) {
  if(b == null) b = 10;
  if(this.signum() == 0 || b < 2 || b > 36) return "0";
  var cs = this.chunkSize(b);
  var a = Math.pow(b,cs);
  var d = nbv(a), y = nbi(), z = nbi(), r = "";
  this.divRemTo(d,y,z);
  while(y.signum() > 0) {
    r = (a+z.intValue()).toString(b).substr(1) + r;
    y.divRemTo(d,y,z);
  }
  return z.intValue().toString(b) + r;
}

// (protected) convert from radix string
function bnpFromRadix(s,b) {
  var self = this;
  self.fromInt(0);
  if(b == null) b = 10;
  var cs = self.chunkSize(b);
  var d = Math.pow(b,cs), mi = false, j = 0, w = 0;
  for(var i = 0; i < s.length; ++i) {
    var x = intAt(s,i);
    if(x < 0) {
      if(s.charAt(i) == "-" && self.signum() == 0) mi = true;
      continue;
    }
    w = b*w+x;
    if(++j >= cs) {
      self.dMultiply(d);
      self.dAddOffset(w,0);
      j = 0;
      w = 0;
    }
  }
  if(j > 0) {
    self.dMultiply(Math.pow(b,j));
    self.dAddOffset(w,0);
  }
  if(mi) BigInteger.ZERO.subTo(self,self);
}

// (protected) alternate constructor
function bnpFromNumber(a,b,c) {
  var self = this;
  if("number" == typeof b) {
    // new BigInteger(int,int,RNG)
    if(a < 2) self.fromInt(1);
    else {
      self.fromNumber(a,c);
      if(!self.testBit(a-1))	// force MSB set
        self.bitwiseTo(BigInteger.ONE.shiftLeft(a-1),op_or,self);
      if(self.isEven()) self.dAddOffset(1,0); // force odd
      while(!self.isProbablePrime(b)) {
        self.dAddOffset(2,0);
        if(self.bitLength() > a) self.subTo(BigInteger.ONE.shiftLeft(a-1),self);
      }
    }
  }
  else {
    // new BigInteger(int,RNG)
    var x = new Array(), t = a&7;
    x.length = (a>>3)+1;
    b.nextBytes(x);
    if(t > 0) x[0] &= ((1<<t)-1); else x[0] = 0;
    self.fromString(x,256);
  }
}

// (public) convert to bigendian byte array
function bnToByteArray() {
  var self = this;
  var i = self.t, r = new Array();
  r[0] = self.s;
  var p = self.DB-(i*self.DB)%8, d, k = 0;
  if(i-- > 0) {
    if(p < self.DB && (d = self[i]>>p) != (self.s&self.DM)>>p)
      r[k++] = d|(self.s<<(self.DB-p));
    while(i >= 0) {
      if(p < 8) {
        d = (self[i]&((1<<p)-1))<<(8-p);
        d |= self[--i]>>(p+=self.DB-8);
      }
      else {
        d = (self[i]>>(p-=8))&0xff;
        if(p <= 0) { p += self.DB; --i; }
      }
      if((d&0x80) != 0) d |= -256;
      if(k === 0 && (self.s&0x80) != (d&0x80)) ++k;
      if(k > 0 || d != self.s) r[k++] = d;
    }
  }
  return r;
}

function bnEquals(a) { return(this.compareTo(a)==0); }
function bnMin(a) { return(this.compareTo(a)<0)?this:a; }
function bnMax(a) { return(this.compareTo(a)>0)?this:a; }

// (protected) r = this op a (bitwise)
function bnpBitwiseTo(a,op,r) {
  var self = this;
  var i, f, m = Math.min(a.t,self.t);
  for(i = 0; i < m; ++i) r[i] = op(self[i],a[i]);
  if(a.t < self.t) {
    f = a.s&self.DM;
    for(i = m; i < self.t; ++i) r[i] = op(self[i],f);
    r.t = self.t;
  }
  else {
    f = self.s&self.DM;
    for(i = m; i < a.t; ++i) r[i] = op(f,a[i]);
    r.t = a.t;
  }
  r.s = op(self.s,a.s);
  r.clamp();
}

// (public) this & a
function op_and(x,y) { return x&y; }
function bnAnd(a) { var r = nbi(); this.bitwiseTo(a,op_and,r); return r; }

// (public) this | a
function op_or(x,y) { return x|y; }
function bnOr(a) { var r = nbi(); this.bitwiseTo(a,op_or,r); return r; }

// (public) this ^ a
function op_xor(x,y) { return x^y; }
function bnXor(a) { var r = nbi(); this.bitwiseTo(a,op_xor,r); return r; }

// (public) this & ~a
function op_andnot(x,y) { return x&~y; }
function bnAndNot(a) { var r = nbi(); this.bitwiseTo(a,op_andnot,r); return r; }

// (public) ~this
function bnNot() {
  var r = nbi();
  for(var i = 0; i < this.t; ++i) r[i] = this.DM&~this[i];
  r.t = this.t;
  r.s = ~this.s;
  return r;
}

// (public) this << n
function bnShiftLeft(n) {
  var r = nbi();
  if(n < 0) this.rShiftTo(-n,r); else this.lShiftTo(n,r);
  return r;
}

// (public) this >> n
function bnShiftRight(n) {
  var r = nbi();
  if(n < 0) this.lShiftTo(-n,r); else this.rShiftTo(n,r);
  return r;
}

// return index of lowest 1-bit in x, x < 2^31
function lbit(x) {
  if(x == 0) return -1;
  var r = 0;
  if((x&0xffff) == 0) { x >>= 16; r += 16; }
  if((x&0xff) == 0) { x >>= 8; r += 8; }
  if((x&0xf) == 0) { x >>= 4; r += 4; }
  if((x&3) == 0) { x >>= 2; r += 2; }
  if((x&1) == 0) ++r;
  return r;
}

// (public) returns index of lowest 1-bit (or -1 if none)
function bnGetLowestSetBit() {
  for(var i = 0; i < this.t; ++i)
    if(this[i] != 0) return i*this.DB+lbit(this[i]);
  if(this.s < 0) return this.t*this.DB;
  return -1;
}

// return number of 1 bits in x
function cbit(x) {
  var r = 0;
  while(x != 0) { x &= x-1; ++r; }
  return r;
}

// (public) return number of set bits
function bnBitCount() {
  var r = 0, x = this.s&this.DM;
  for(var i = 0; i < this.t; ++i) r += cbit(this[i]^x);
  return r;
}

// (public) true iff nth bit is set
function bnTestBit(n) {
  var j = Math.floor(n/this.DB);
  if(j >= this.t) return(this.s!=0);
  return((this[j]&(1<<(n%this.DB)))!=0);
}

// (protected) this op (1<<n)
function bnpChangeBit(n,op) {
  var r = BigInteger.ONE.shiftLeft(n);
  this.bitwiseTo(r,op,r);
  return r;
}

// (public) this | (1<<n)
function bnSetBit(n) { return this.changeBit(n,op_or); }

// (public) this & ~(1<<n)
function bnClearBit(n) { return this.changeBit(n,op_andnot); }

// (public) this ^ (1<<n)
function bnFlipBit(n) { return this.changeBit(n,op_xor); }

// (protected) r = this + a
function bnpAddTo(a,r) {
  var self = this;

  var i = 0, c = 0, m = Math.min(a.t,self.t);
  while(i < m) {
    c += self[i]+a[i];
    r[i++] = c&self.DM;
    c >>= self.DB;
  }
  if(a.t < self.t) {
    c += a.s;
    while(i < self.t) {
      c += self[i];
      r[i++] = c&self.DM;
      c >>= self.DB;
    }
    c += self.s;
  }
  else {
    c += self.s;
    while(i < a.t) {
      c += a[i];
      r[i++] = c&self.DM;
      c >>= self.DB;
    }
    c += a.s;
  }
  r.s = (c<0)?-1:0;
  if(c > 0) r[i++] = c;
  else if(c < -1) r[i++] = self.DV+c;
  r.t = i;
  r.clamp();
}

// (public) this + a
function bnAdd(a) { var r = nbi(); this.addTo(a,r); return r; }

// (public) this - a
function bnSubtract(a) { var r = nbi(); this.subTo(a,r); return r; }

// (public) this * a
function bnMultiply(a) { var r = nbi(); this.multiplyTo(a,r); return r; }

// (public) this^2
function bnSquare() { var r = nbi(); this.squareTo(r); return r; }

// (public) this / a
function bnDivide(a) { var r = nbi(); this.divRemTo(a,r,null); return r; }

// (public) this % a
function bnRemainder(a) { var r = nbi(); this.divRemTo(a,null,r); return r; }

// (public) [this/a,this%a]
function bnDivideAndRemainder(a) {
  var q = nbi(), r = nbi();
  this.divRemTo(a,q,r);
  return new Array(q,r);
}

// (protected) this *= n, this >= 0, 1 < n < DV
function bnpDMultiply(n) {
  this[this.t] = this.am(0,n-1,this,0,0,this.t);
  ++this.t;
  this.clamp();
}

// (protected) this += n << w words, this >= 0
function bnpDAddOffset(n,w) {
  if(n == 0) return;
  while(this.t <= w) this[this.t++] = 0;
  this[w] += n;
  while(this[w] >= this.DV) {
    this[w] -= this.DV;
    if(++w >= this.t) this[this.t++] = 0;
    ++this[w];
  }
}

// A "null" reducer
function NullExp() {}
function nNop(x) { return x; }
function nMulTo(x,y,r) { x.multiplyTo(y,r); }
function nSqrTo(x,r) { x.squareTo(r); }

NullExp.prototype.convert = nNop;
NullExp.prototype.revert = nNop;
NullExp.prototype.mulTo = nMulTo;
NullExp.prototype.sqrTo = nSqrTo;

// (public) this^e
function bnPow(e) { return this.exp(e,new NullExp()); }

// (protected) r = lower n words of "this * a", a.t <= n
// "this" should be the larger one if appropriate.
function bnpMultiplyLowerTo(a,n,r) {
  var i = Math.min(this.t+a.t,n);
  r.s = 0; // assumes a,this >= 0
  r.t = i;
  while(i > 0) r[--i] = 0;
  var j;
  for(j = r.t-this.t; i < j; ++i) r[i+this.t] = this.am(0,a[i],r,i,0,this.t);
  for(j = Math.min(a.t,n); i < j; ++i) this.am(0,a[i],r,i,0,n-i);
  r.clamp();
}

// (protected) r = "this * a" without lower n words, n > 0
// "this" should be the larger one if appropriate.
function bnpMultiplyUpperTo(a,n,r) {
  --n;
  var i = r.t = this.t+a.t-n;
  r.s = 0; // assumes a,this >= 0
  while(--i >= 0) r[i] = 0;
  for(i = Math.max(n-this.t,0); i < a.t; ++i)
    r[this.t+i-n] = this.am(n-i,a[i],r,0,0,this.t+i-n);
  r.clamp();
  r.drShiftTo(1,r);
}

// Barrett modular reduction
function Barrett(m) {
  // setup Barrett
  this.r2 = nbi();
  this.q3 = nbi();
  BigInteger.ONE.dlShiftTo(2*m.t,this.r2);
  this.mu = this.r2.divide(m);
  this.m = m;
}

function barrettConvert(x) {
  if(x.s < 0 || x.t > 2*this.m.t) return x.mod(this.m);
  else if(x.compareTo(this.m) < 0) return x;
  else { var r = nbi(); x.copyTo(r); this.reduce(r); return r; }
}

function barrettRevert(x) { return x; }

// x = x mod m (HAC 14.42)
function barrettReduce(x) {
  var self = this;
  x.drShiftTo(self.m.t-1,self.r2);
  if(x.t > self.m.t+1) { x.t = self.m.t+1; x.clamp(); }
  self.mu.multiplyUpperTo(self.r2,self.m.t+1,self.q3);
  self.m.multiplyLowerTo(self.q3,self.m.t+1,self.r2);
  while(x.compareTo(self.r2) < 0) x.dAddOffset(1,self.m.t+1);
  x.subTo(self.r2,x);
  while(x.compareTo(self.m) >= 0) x.subTo(self.m,x);
}

// r = x^2 mod m; x != r
function barrettSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

// r = x*y mod m; x,y != r
function barrettMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }

Barrett.prototype.convert = barrettConvert;
Barrett.prototype.revert = barrettRevert;
Barrett.prototype.reduce = barrettReduce;
Barrett.prototype.mulTo = barrettMulTo;
Barrett.prototype.sqrTo = barrettSqrTo;

// (public) this^e % m (HAC 14.85)
function bnModPow(e,m) {
  var i = e.bitLength(), k, r = nbv(1), z;
  if(i <= 0) return r;
  else if(i < 18) k = 1;
  else if(i < 48) k = 3;
  else if(i < 144) k = 4;
  else if(i < 768) k = 5;
  else k = 6;
  if(i < 8)
    z = new Classic(m);
  else if(m.isEven())
    z = new Barrett(m);
  else
    z = new Montgomery(m);

  // precomputation
  var g = new Array(), n = 3, k1 = k-1, km = (1<<k)-1;
  g[1] = z.convert(this);
  if(k > 1) {
    var g2 = nbi();
    z.sqrTo(g[1],g2);
    while(n <= km) {
      g[n] = nbi();
      z.mulTo(g2,g[n-2],g[n]);
      n += 2;
    }
  }

  var j = e.t-1, w, is1 = true, r2 = nbi(), t;
  i = nbits(e[j])-1;
  while(j >= 0) {
    if(i >= k1) w = (e[j]>>(i-k1))&km;
    else {
      w = (e[j]&((1<<(i+1))-1))<<(k1-i);
      if(j > 0) w |= e[j-1]>>(this.DB+i-k1);
    }

    n = k;
    while((w&1) == 0) { w >>= 1; --n; }
    if((i -= n) < 0) { i += this.DB; --j; }
    if(is1) {	// ret == 1, don't bother squaring or multiplying it
      g[w].copyTo(r);
      is1 = false;
    }
    else {
      while(n > 1) { z.sqrTo(r,r2); z.sqrTo(r2,r); n -= 2; }
      if(n > 0) z.sqrTo(r,r2); else { t = r; r = r2; r2 = t; }
      z.mulTo(r2,g[w],r);
    }

    while(j >= 0 && (e[j]&(1<<i)) == 0) {
      z.sqrTo(r,r2); t = r; r = r2; r2 = t;
      if(--i < 0) { i = this.DB-1; --j; }
    }
  }
  return z.revert(r);
}

// (public) gcd(this,a) (HAC 14.54)
function bnGCD(a) {
  var x = (this.s<0)?this.negate():this.clone();
  var y = (a.s<0)?a.negate():a.clone();
  if(x.compareTo(y) < 0) { var t = x; x = y; y = t; }
  var i = x.getLowestSetBit(), g = y.getLowestSetBit();
  if(g < 0) return x;
  if(i < g) g = i;
  if(g > 0) {
    x.rShiftTo(g,x);
    y.rShiftTo(g,y);
  }
  while(x.signum() > 0) {
    if((i = x.getLowestSetBit()) > 0) x.rShiftTo(i,x);
    if((i = y.getLowestSetBit()) > 0) y.rShiftTo(i,y);
    if(x.compareTo(y) >= 0) {
      x.subTo(y,x);
      x.rShiftTo(1,x);
    }
    else {
      y.subTo(x,y);
      y.rShiftTo(1,y);
    }
  }
  if(g > 0) y.lShiftTo(g,y);
  return y;
}

// (protected) this % n, n < 2^26
function bnpModInt(n) {
  if(n <= 0) return 0;
  var d = this.DV%n, r = (this.s<0)?n-1:0;
  if(this.t > 0)
    if(d == 0) r = this[0]%n;
    else for(var i = this.t-1; i >= 0; --i) r = (d*r+this[i])%n;
  return r;
}

// (public) 1/this % m (HAC 14.61)
function bnModInverse(m) {
  var ac = m.isEven();
  if((this.isEven() && ac) || m.signum() == 0) return BigInteger.ZERO;
  var u = m.clone(), v = this.clone();
  var a = nbv(1), b = nbv(0), c = nbv(0), d = nbv(1);
  while(u.signum() != 0) {
    while(u.isEven()) {
      u.rShiftTo(1,u);
      if(ac) {
        if(!a.isEven() || !b.isEven()) { a.addTo(this,a); b.subTo(m,b); }
        a.rShiftTo(1,a);
      }
      else if(!b.isEven()) b.subTo(m,b);
      b.rShiftTo(1,b);
    }
    while(v.isEven()) {
      v.rShiftTo(1,v);
      if(ac) {
        if(!c.isEven() || !d.isEven()) { c.addTo(this,c); d.subTo(m,d); }
        c.rShiftTo(1,c);
      }
      else if(!d.isEven()) d.subTo(m,d);
      d.rShiftTo(1,d);
    }
    if(u.compareTo(v) >= 0) {
      u.subTo(v,u);
      if(ac) a.subTo(c,a);
      b.subTo(d,b);
    }
    else {
      v.subTo(u,v);
      if(ac) c.subTo(a,c);
      d.subTo(b,d);
    }
  }
  if(v.compareTo(BigInteger.ONE) != 0) return BigInteger.ZERO;
  if(d.compareTo(m) >= 0) return d.subtract(m);
  if(d.signum() < 0) d.addTo(m,d); else return d;
  if(d.signum() < 0) return d.add(m); else return d;
}

// protected
proto.chunkSize = bnpChunkSize;
proto.toRadix = bnpToRadix;
proto.fromRadix = bnpFromRadix;
proto.fromNumber = bnpFromNumber;
proto.bitwiseTo = bnpBitwiseTo;
proto.changeBit = bnpChangeBit;
proto.addTo = bnpAddTo;
proto.dMultiply = bnpDMultiply;
proto.dAddOffset = bnpDAddOffset;
proto.multiplyLowerTo = bnpMultiplyLowerTo;
proto.multiplyUpperTo = bnpMultiplyUpperTo;
proto.modInt = bnpModInt;

// public
proto.clone = bnClone;
proto.intValue = bnIntValue;
proto.byteValue = bnByteValue;
proto.shortValue = bnShortValue;
proto.signum = bnSigNum;
proto.toByteArray = bnToByteArray;
proto.equals = bnEquals;
proto.min = bnMin;
proto.max = bnMax;
proto.and = bnAnd;
proto.or = bnOr;
proto.xor = bnXor;
proto.andNot = bnAndNot;
proto.not = bnNot;
proto.shiftLeft = bnShiftLeft;
proto.shiftRight = bnShiftRight;
proto.getLowestSetBit = bnGetLowestSetBit;
proto.bitCount = bnBitCount;
proto.testBit = bnTestBit;
proto.setBit = bnSetBit;
proto.clearBit = bnClearBit;
proto.flipBit = bnFlipBit;
proto.add = bnAdd;
proto.subtract = bnSubtract;
proto.multiply = bnMultiply;
proto.divide = bnDivide;
proto.remainder = bnRemainder;
proto.divideAndRemainder = bnDivideAndRemainder;
proto.modPow = bnModPow;
proto.modInverse = bnModInverse;
proto.pow = bnPow;
proto.gcd = bnGCD;

// JSBN-specific extension
proto.square = bnSquare;

// BigInteger interfaces not implemented in jsbn:

// BigInteger(int signum, byte[] magnitude)
// double doubleValue()
// float floatValue()
// int hashCode()
// long longValue()
// static BigInteger valueOf(long val)

// "constants"
BigInteger.ZERO = nbv(0);
BigInteger.ONE = nbv(1);
BigInteger.valueOf = nbv;


/// bitcoinjs addons

/**
 * Turns a byte array into a big integer.
 *
 * This function will interpret a byte array as a big integer in big
 * endian notation and ignore leading zeros.
 */
BigInteger.fromByteArrayUnsigned = function(ba) {

  if (!ba.length) {
    return new BigInteger.valueOf(0);
  } else if (ba[0] & 0x80) {
    // Prepend a zero so the BigInteger class doesn't mistake this
    // for a negative integer.
    return new BigInteger([0].concat(ba));
  } else {
    return new BigInteger(ba);
  }
};

/**
 * Parse a signed big integer byte representation.
 *
 * For details on the format please see BigInteger.toByteArraySigned.
 */
BigInteger.fromByteArraySigned = function(ba) {
  // Check for negative value
  if (ba[0] & 0x80) {
    // Remove sign bit
    ba[0] &= 0x7f;

    return BigInteger.fromByteArrayUnsigned(ba).negate();
  } else {
    return BigInteger.fromByteArrayUnsigned(ba);
  }
};

/**
 * Returns a byte array representation of the big integer.
 *
 * This returns the absolute of the contained value in big endian
 * form. A value of zero results in an empty array.
 */
BigInteger.prototype.toByteArrayUnsigned = function() {
    var ba = this.abs().toByteArray();

    // Empty array, nothing to do
    if (!ba.length) {
        return ba;
    }

    // remove leading 0
    if (ba[0] === 0) {
        ba = ba.slice(1);
    }

    // all values must be positive
    for (var i=0 ; i<ba.length ; ++i) {
      ba[i] = (ba[i] < 0) ? ba[i] + 256 : ba[i];
    }

    return ba;
};

/*
 * Converts big integer to signed byte representation.
 *
 * The format for this value uses the most significant bit as a sign
 * bit. If the most significant bit is already occupied by the
 * absolute value, an extra byte is prepended and the sign bit is set
 * there.
 *
 * Examples:
 *
 *      0 =>     0x00
 *      1 =>     0x01
 *     -1 =>     0x81
 *    127 =>     0x7f
 *   -127 =>     0xff
 *    128 =>   0x0080
 *   -128 =>   0x8080
 *    255 =>   0x00ff
 *   -255 =>   0x80ff
 *  16300 =>   0x3fac
 * -16300 =>   0xbfac
 *  62300 => 0x00f35c
 * -62300 => 0x80f35c
*/
BigInteger.prototype.toByteArraySigned = function() {
  var val = this.toByteArrayUnsigned();
  var neg = this.s < 0;

  // if the first bit is set, we always unshift
  // either unshift 0x80 or 0x00
  if (val[0] & 0x80) {
    val.unshift((neg) ? 0x80 : 0x00);
  }
  // if the first bit isn't set, set it if negative
  else if (neg) {
    val[0] |= 0x80;
  }

  return val;
};
 //next 


//start 

 /*!
* Basic Javascript Elliptic Curve implementation
* Ported loosely from BouncyCastle's Java EC code
* Only Fp curves implemented for now
* 
* Copyright Tom Wu, bitaddress.org  BSD License.
* http://www-cs-students.stanford.edu/~tjw/jsbn/LICENSE
*/
(function () {

	// Constructor function of Global EllipticCurve object
	var ec = window.EllipticCurve = function () { };


	// ----------------
	// ECFieldElementFp constructor
	// q instanceof BigInteger
	// x instanceof BigInteger
	ec.FieldElementFp = function (q, x) {
		this.x = x;
		// TODO if(x.compareTo(q) >= 0) error
		this.q = q;
	};

	ec.FieldElementFp.prototype.equals = function (other) {
		if (other == this) return true;
		return (this.q.equals(other.q) && this.x.equals(other.x));
	};

	ec.FieldElementFp.prototype.toBigInteger = function () {
		return this.x;
	};

	ec.FieldElementFp.prototype.negate = function () {
		return new ec.FieldElementFp(this.q, this.x.negate().mod(this.q));
	};

	ec.FieldElementFp.prototype.add = function (b) {
		return new ec.FieldElementFp(this.q, this.x.add(b.toBigInteger()).mod(this.q));
	};

	ec.FieldElementFp.prototype.subtract = function (b) {
		return new ec.FieldElementFp(this.q, this.x.subtract(b.toBigInteger()).mod(this.q));
	};

	ec.FieldElementFp.prototype.multiply = function (b) {
		return new ec.FieldElementFp(this.q, this.x.multiply(b.toBigInteger()).mod(this.q));
	};

	ec.FieldElementFp.prototype.square = function () {
		return new ec.FieldElementFp(this.q, this.x.square().mod(this.q));
	};

	ec.FieldElementFp.prototype.divide = function (b) {
		return new ec.FieldElementFp(this.q, this.x.multiply(b.toBigInteger().modInverse(this.q)).mod(this.q));
	};

	ec.FieldElementFp.prototype.getByteLength = function () {
		return Math.floor((this.toBigInteger().bitLength() + 7) / 8);
	};

	// D.1.4 91
	/**
	* return a sqrt root - the routine verifies that the calculation
	* returns the right value - if none exists it returns null.
	* 
	* Copyright (c) 2000 - 2011 The Legion Of The Bouncy Castle (http://www.bouncycastle.org)
	* Ported to JavaScript by bitaddress.org
	*/
	ec.FieldElementFp.prototype.sqrt = function () {
		if (!this.q.testBit(0)) throw new Error("even value of q");

		// p mod 4 == 3
		if (this.q.testBit(1)) {
			// z = g^(u+1) + p, p = 4u + 3
			var z = new ec.FieldElementFp(this.q, this.x.modPow(this.q.shiftRight(2).add(BigInteger.ONE), this.q));
			return z.square().equals(this) ? z : null;
		}

		// p mod 4 == 1
		var qMinusOne = this.q.subtract(BigInteger.ONE);
		var legendreExponent = qMinusOne.shiftRight(1);
		if (!(this.x.modPow(legendreExponent, this.q).equals(BigInteger.ONE))) return null;
		var u = qMinusOne.shiftRight(2);
		var k = u.shiftLeft(1).add(BigInteger.ONE);
		var Q = this.x;
		var fourQ = Q.shiftLeft(2).mod(this.q);
		var U, V;

		do {
			var rand = new SecureRandom();
			var P;
			do {
				P = new BigInteger(this.q.bitLength(), rand);
			}
			while (P.compareTo(this.q) >= 0 || !(P.multiply(P).subtract(fourQ).modPow(legendreExponent, this.q).equals(qMinusOne)));

			var result = ec.FieldElementFp.fastLucasSequence(this.q, P, Q, k);

			U = result[0];
			V = result[1];
			if (V.multiply(V).mod(this.q).equals(fourQ)) {
				// Integer division by 2, mod q
				if (V.testBit(0)) {
					V = V.add(this.q);
				}
				V = V.shiftRight(1);
				return new ec.FieldElementFp(this.q, V);
			}
		}
		while (U.equals(BigInteger.ONE) || U.equals(qMinusOne));

		return null;
	};

	/*
	* Copyright (c) 2000 - 2011 The Legion Of The Bouncy Castle (http://www.bouncycastle.org)
	* Ported to JavaScript by bitaddress.org
	*/
	ec.FieldElementFp.fastLucasSequence = function (p, P, Q, k) {
		// TODO Research and apply "common-multiplicand multiplication here"

		var n = k.bitLength();
		var s = k.getLowestSetBit();
		var Uh = BigInteger.ONE;
		var Vl = BigInteger.TWO;
		var Vh = P;
		var Ql = BigInteger.ONE;
		var Qh = BigInteger.ONE;

		for (var j = n - 1; j >= s + 1; --j) {
			Ql = Ql.multiply(Qh).mod(p);
			if (k.testBit(j)) {
				Qh = Ql.multiply(Q).mod(p);
				Uh = Uh.multiply(Vh).mod(p);
				Vl = Vh.multiply(Vl).subtract(P.multiply(Ql)).mod(p);
				Vh = Vh.multiply(Vh).subtract(Qh.shiftLeft(1)).mod(p);
			}
			else {
				Qh = Ql;
				Uh = Uh.multiply(Vl).subtract(Ql).mod(p);
				Vh = Vh.multiply(Vl).subtract(P.multiply(Ql)).mod(p);
				Vl = Vl.multiply(Vl).subtract(Ql.shiftLeft(1)).mod(p);
			}
		}

		Ql = Ql.multiply(Qh).mod(p);
		Qh = Ql.multiply(Q).mod(p);
		Uh = Uh.multiply(Vl).subtract(Ql).mod(p);
		Vl = Vh.multiply(Vl).subtract(P.multiply(Ql)).mod(p);
		Ql = Ql.multiply(Qh).mod(p);

		for (var j = 1; j <= s; ++j) {
			Uh = Uh.multiply(Vl).mod(p);
			Vl = Vl.multiply(Vl).subtract(Ql.shiftLeft(1)).mod(p);
			Ql = Ql.multiply(Ql).mod(p);
		}

		return [Uh, Vl];
	};

	// ----------------
	// ECPointFp constructor
	ec.PointFp = function (curve, x, y, z, compressed) {
		this.curve = curve;
		this.x = x;
		this.y = y;
		// Projective coordinates: either zinv == null or z * zinv == 1
		// z and zinv are just BigIntegers, not fieldElements
		if (z == null) {
			this.z = BigInteger.ONE;
		}
		else {
			this.z = z;
		}
		this.zinv = null;
		// compression flag
		this.compressed = !!compressed;
	};

	ec.PointFp.prototype.getX = function () {
		if (this.zinv == null) {
			this.zinv = this.z.modInverse(this.curve.q);
		}
		var r = this.x.toBigInteger().multiply(this.zinv);
		this.curve.reduce(r);
		return this.curve.fromBigInteger(r);
	};

	ec.PointFp.prototype.getY = function () {
		if (this.zinv == null) {
			this.zinv = this.z.modInverse(this.curve.q);
		}
		var r = this.y.toBigInteger().multiply(this.zinv);
		this.curve.reduce(r);
		return this.curve.fromBigInteger(r);
	};

	ec.PointFp.prototype.equals = function (other) {
		if (other == this) return true;
		if (this.isInfinity()) return other.isInfinity();
		if (other.isInfinity()) return this.isInfinity();
		var u, v;
		// u = Y2 * Z1 - Y1 * Z2
		u = other.y.toBigInteger().multiply(this.z).subtract(this.y.toBigInteger().multiply(other.z)).mod(this.curve.q);
		if (!u.equals(BigInteger.ZERO)) return false;
		// v = X2 * Z1 - X1 * Z2
		v = other.x.toBigInteger().multiply(this.z).subtract(this.x.toBigInteger().multiply(other.z)).mod(this.curve.q);
		return v.equals(BigInteger.ZERO);
	};

	ec.PointFp.prototype.isInfinity = function () {
		if ((this.x == null) && (this.y == null)) return true;
		return this.z.equals(BigInteger.ZERO) && !this.y.toBigInteger().equals(BigInteger.ZERO);
	};

	ec.PointFp.prototype.negate = function () {
		return new ec.PointFp(this.curve, this.x, this.y.negate(), this.z);
	};

	ec.PointFp.prototype.add = function (b) {
		if (this.isInfinity()) return b;
		if (b.isInfinity()) return this;

		// u = Y2 * Z1 - Y1 * Z2
		var u = b.y.toBigInteger().multiply(this.z).subtract(this.y.toBigInteger().multiply(b.z)).mod(this.curve.q);
		// v = X2 * Z1 - X1 * Z2
		var v = b.x.toBigInteger().multiply(this.z).subtract(this.x.toBigInteger().multiply(b.z)).mod(this.curve.q);


		if (BigInteger.ZERO.equals(v)) {
			if (BigInteger.ZERO.equals(u)) {
				return this.twice(); // this == b, so double
			}
			return this.curve.getInfinity(); // this = -b, so infinity
		}

		var THREE = new BigInteger("3");
		var x1 = this.x.toBigInteger();
		var y1 = this.y.toBigInteger();
		var x2 = b.x.toBigInteger();
		var y2 = b.y.toBigInteger();

		var v2 = v.square();
		var v3 = v2.multiply(v);
		var x1v2 = x1.multiply(v2);
		var zu2 = u.square().multiply(this.z);

		// x3 = v * (z2 * (z1 * u^2 - 2 * x1 * v^2) - v^3)
		var x3 = zu2.subtract(x1v2.shiftLeft(1)).multiply(b.z).subtract(v3).multiply(v).mod(this.curve.q);
		// y3 = z2 * (3 * x1 * u * v^2 - y1 * v^3 - z1 * u^3) + u * v^3
		var y3 = x1v2.multiply(THREE).multiply(u).subtract(y1.multiply(v3)).subtract(zu2.multiply(u)).multiply(b.z).add(u.multiply(v3)).mod(this.curve.q);
		// z3 = v^3 * z1 * z2
		var z3 = v3.multiply(this.z).multiply(b.z).mod(this.curve.q);

		return new ec.PointFp(this.curve, this.curve.fromBigInteger(x3), this.curve.fromBigInteger(y3), z3);
	};

	ec.PointFp.prototype.twice = function () {
		if (this.isInfinity()) return this;
		if (this.y.toBigInteger().signum() == 0) return this.curve.getInfinity();

		// TODO: optimized handling of constants
		var THREE = new BigInteger("3");
		var x1 = this.x.toBigInteger();
		var y1 = this.y.toBigInteger();

		var y1z1 = y1.multiply(this.z);
		var y1sqz1 = y1z1.multiply(y1).mod(this.curve.q);
		var a = this.curve.a.toBigInteger();

		// w = 3 * x1^2 + a * z1^2
		var w = x1.square().multiply(THREE);
		if (!BigInteger.ZERO.equals(a)) {
			w = w.add(this.z.square().multiply(a));
		}
		w = w.mod(this.curve.q);
		//this.curve.reduce(w);
		// x3 = 2 * y1 * z1 * (w^2 - 8 * x1 * y1^2 * z1)
		var x3 = w.square().subtract(x1.shiftLeft(3).multiply(y1sqz1)).shiftLeft(1).multiply(y1z1).mod(this.curve.q);
		// y3 = 4 * y1^2 * z1 * (3 * w * x1 - 2 * y1^2 * z1) - w^3
		var y3 = w.multiply(THREE).multiply(x1).subtract(y1sqz1.shiftLeft(1)).shiftLeft(2).multiply(y1sqz1).subtract(w.square().multiply(w)).mod(this.curve.q);
		// z3 = 8 * (y1 * z1)^3
		var z3 = y1z1.square().multiply(y1z1).shiftLeft(3).mod(this.curve.q);

		return new ec.PointFp(this.curve, this.curve.fromBigInteger(x3), this.curve.fromBigInteger(y3), z3);
	};

	// Simple NAF (Non-Adjacent Form) multiplication algorithm
	// TODO: modularize the multiplication algorithm
	ec.PointFp.prototype.multiply = function (k) {
		if (this.isInfinity()) return this;
		if (k.signum() == 0) return this.curve.getInfinity();

		var e = k;
		var h = e.multiply(new BigInteger("3"));

		var neg = this.negate();
		var R = this;

		var i;
		for (i = h.bitLength() - 2; i > 0; --i) {
			R = R.twice();

			var hBit = h.testBit(i);
			var eBit = e.testBit(i);

			if (hBit != eBit) {
				R = R.add(hBit ? this : neg);
			}
		}

		return R;
	};

	// Compute this*j + x*k (simultaneous multiplication)
	ec.PointFp.prototype.multiplyTwo = function (j, x, k) {
		var i;
		if (j.bitLength() > k.bitLength())
			i = j.bitLength() - 1;
		else
			i = k.bitLength() - 1;

		var R = this.curve.getInfinity();
		var both = this.add(x);
		while (i >= 0) {
			R = R.twice();
			if (j.testBit(i)) {
				if (k.testBit(i)) {
					R = R.add(both);
				}
				else {
					R = R.add(this);
				}
			}
			else {
				if (k.testBit(i)) {
					R = R.add(x);
				}
			}
			--i;
		}

		return R;
	};

	// patched by bitaddress.org and Casascius for use with Bitcoin.ECKey
	// patched by coretechs to support compressed public keys
	ec.PointFp.prototype.getEncoded = function (compressed) {
		var x = this.getX().toBigInteger();
		var y = this.getY().toBigInteger();
		var len = 32; // integerToBytes will zero pad if integer is less than 32 bytes. 32 bytes length is required by the Bitcoin protocol.
		var enc = ec.integerToBytes(x, len);

		// when compressed prepend byte depending if y point is even or odd 
		if (compressed) {
			if (y.isEven()) {
				enc.unshift(0x02);
			}
			else {
				enc.unshift(0x03);
			}
		}
		else {
			enc.unshift(0x04);
			enc = enc.concat(ec.integerToBytes(y, len)); // uncompressed public key appends the bytes of the y point
		}
		return enc;
	};

	ec.PointFp.decodeFrom = function (curve, enc) {
		var type = enc[0];
		var dataLen = enc.length - 1;

		// Extract x and y as byte arrays
		var xBa = enc.slice(1, 1 + dataLen / 2);
		var yBa = enc.slice(1 + dataLen / 2, 1 + dataLen);

		// Prepend zero byte to prevent interpretation as negative integer
		xBa.unshift(0);
		yBa.unshift(0);

		// Convert to BigIntegers
		var x = new BigInteger(xBa);
		var y = new BigInteger(yBa);

		// Return point
		return new ec.PointFp(curve, curve.fromBigInteger(x), curve.fromBigInteger(y));
	};

	ec.PointFp.prototype.add2D = function (b) {
		if (this.isInfinity()) return b;
		if (b.isInfinity()) return this;

		if (this.x.equals(b.x)) {
			if (this.y.equals(b.y)) {
				// this = b, i.e. this must be doubled
				return this.twice();
			}
			// this = -b, i.e. the result is the point at infinity
			return this.curve.getInfinity();
		}

		var x_x = b.x.subtract(this.x);
		var y_y = b.y.subtract(this.y);
		var gamma = y_y.divide(x_x);

		var x3 = gamma.square().subtract(this.x).subtract(b.x);
		var y3 = gamma.multiply(this.x.subtract(x3)).subtract(this.y);

		return new ec.PointFp(this.curve, x3, y3);
	};

	ec.PointFp.prototype.twice2D = function () {
		if (this.isInfinity()) return this;
		if (this.y.toBigInteger().signum() == 0) {
			// if y1 == 0, then (x1, y1) == (x1, -y1)
			// and hence this = -this and thus 2(x1, y1) == infinity
			return this.curve.getInfinity();
		}

		var TWO = this.curve.fromBigInteger(BigInteger.valueOf(2));
		var THREE = this.curve.fromBigInteger(BigInteger.valueOf(3));
		var gamma = this.x.square().multiply(THREE).add(this.curve.a).divide(this.y.multiply(TWO));

		var x3 = gamma.square().subtract(this.x.multiply(TWO));
		var y3 = gamma.multiply(this.x.subtract(x3)).subtract(this.y);

		return new ec.PointFp(this.curve, x3, y3);
	};

	ec.PointFp.prototype.multiply2D = function (k) {
		if (this.isInfinity()) return this;
		if (k.signum() == 0) return this.curve.getInfinity();

		var e = k;
		var h = e.multiply(new BigInteger("3"));

		var neg = this.negate();
		var R = this;

		var i;
		for (i = h.bitLength() - 2; i > 0; --i) {
			R = R.twice();

			var hBit = h.testBit(i);
			var eBit = e.testBit(i);

			if (hBit != eBit) {
				R = R.add2D(hBit ? this : neg);
			}
		}

		return R;
	};

	ec.PointFp.prototype.isOnCurve = function () {
		var x = this.getX().toBigInteger();
		var y = this.getY().toBigInteger();
		var a = this.curve.getA().toBigInteger();
		var b = this.curve.getB().toBigInteger();
		var n = this.curve.getQ();
		var lhs = y.multiply(y).mod(n);
		var rhs = x.multiply(x).multiply(x).add(a.multiply(x)).add(b).mod(n);
		return lhs.equals(rhs);
	};

	ec.PointFp.prototype.toString = function () {
		return '(' + this.getX().toBigInteger().toString() + ',' + this.getY().toBigInteger().toString() + ')';
	};

	/**
	* Validate an elliptic curve point.
	*
	* See SEC 1, section 3.2.2.1: Elliptic Curve Public Key Validation Primitive
	*/
	ec.PointFp.prototype.validate = function () {
		var n = this.curve.getQ();

		// Check Q != O
		if (this.isInfinity()) {
			throw new Error("Point is at infinity.");
		}

		// Check coordinate bounds
		var x = this.getX().toBigInteger();
		var y = this.getY().toBigInteger();
		if (x.compareTo(BigInteger.ONE) < 0 || x.compareTo(n.subtract(BigInteger.ONE)) > 0) {
			throw new Error('x coordinate out of bounds');
		}
		if (y.compareTo(BigInteger.ONE) < 0 || y.compareTo(n.subtract(BigInteger.ONE)) > 0) {
			throw new Error('y coordinate out of bounds');
		}

		// Check y^2 = x^3 + ax + b (mod n)
		if (!this.isOnCurve()) {
			throw new Error("Point is not on the curve.");
		}

		// Check nQ = 0 (Q is a scalar multiple of G)
		if (this.multiply(n).isInfinity()) {
			// TODO: This check doesn't work - fix.
			throw new Error("Point is not a scalar multiple of G.");
		}

		return true;
	};




	// ----------------
	// ECCurveFp constructor
	ec.CurveFp = function (q, a, b) {
		this.q = q;
		this.a = this.fromBigInteger(a);
		this.b = this.fromBigInteger(b);
		this.infinity = new ec.PointFp(this, null, null);
		this.reducer = new Barrett(this.q);
	}

	ec.CurveFp.prototype.getQ = function () {
		return this.q;
	};

	ec.CurveFp.prototype.getA = function () {
		return this.a;
	};

	ec.CurveFp.prototype.getB = function () {
		return this.b;
	};

	ec.CurveFp.prototype.equals = function (other) {
		if (other == this) return true;
		return (this.q.equals(other.q) && this.a.equals(other.a) && this.b.equals(other.b));
	};

	ec.CurveFp.prototype.getInfinity = function () {
		return this.infinity;
	};

	ec.CurveFp.prototype.fromBigInteger = function (x) {
		return new ec.FieldElementFp(this.q, x);
	};

	ec.CurveFp.prototype.reduce = function (x) {
		this.reducer.reduce(x);
	};

	// for now, work with hex strings because they're easier in JS
	// compressed support added by bitaddress.org
	ec.CurveFp.prototype.decodePointHex = function (s) {
		var firstByte = parseInt(s.substr(0, 2), 16);
		switch (firstByte) { // first byte
			case 0:
				return this.infinity;
			case 2: // compressed
			case 3: // compressed
				var yTilde = firstByte & 1;
				var xHex = s.substr(2, s.length - 2);
				var X1 = new BigInteger(xHex, 16);
				return this.decompressPoint(yTilde, X1);
			case 4: // uncompressed
			case 6: // hybrid
			case 7: // hybrid
				var len = (s.length - 2) / 2;
				var xHex = s.substr(2, len);
				var yHex = s.substr(len + 2, len);

				return new ec.PointFp(this,
					this.fromBigInteger(new BigInteger(xHex, 16)),
					this.fromBigInteger(new BigInteger(yHex, 16)));

			default: // unsupported
				return null;
		}
	};

	ec.CurveFp.prototype.encodePointHex = function (p) {
		if (p.isInfinity()) return "00";
		var xHex = p.getX().toBigInteger().toString(16);
		var yHex = p.getY().toBigInteger().toString(16);
		var oLen = this.getQ().toString(16).length;
		if ((oLen % 2) != 0) oLen++;
		while (xHex.length < oLen) {
			xHex = "0" + xHex;
		}
		while (yHex.length < oLen) {
			yHex = "0" + yHex;
		}
		return "04" + xHex + yHex;
	};

	/*
	* Copyright (c) 2000 - 2011 The Legion Of The Bouncy Castle (http://www.bouncycastle.org)
	* Ported to JavaScript by bitaddress.org
	*
	* Number yTilde
	* BigInteger X1
	*/
	ec.CurveFp.prototype.decompressPoint = function (yTilde, X1) {
		var x = this.fromBigInteger(X1);
		var alpha = x.multiply(x.square().add(this.getA())).add(this.getB());
		var beta = alpha.sqrt();
		// if we can't find a sqrt we haven't got a point on the curve - run!
		if (beta == null) throw new Error("Invalid point compression");
		var betaValue = beta.toBigInteger();
		var bit0 = betaValue.testBit(0) ? 1 : 0;
		if (bit0 != yTilde) {
			// Use the other root
			beta = this.fromBigInteger(this.getQ().subtract(betaValue));
		}
		return new ec.PointFp(this, x, beta, null, true);
	};


	ec.fromHex = function (s) { return new BigInteger(s, 16); };

	ec.integerToBytes = function (i, len) {
		var bytes = i.toByteArrayUnsigned();
		if (len < bytes.length) {
			bytes = bytes.slice(bytes.length - len);
		} else while (len > bytes.length) {
			bytes.unshift(0);
		}
		return bytes;
	};


	// Named EC curves
	// ----------------
	// X9ECParameters constructor
	ec.X9Parameters = function (curve, g, n, h) {
		this.curve = curve;
		this.g = g;
		this.n = n;
		this.h = h;
	}
	ec.X9Parameters.prototype.getCurve = function () { return this.curve; };
	ec.X9Parameters.prototype.getG = function () { return this.g; };
	ec.X9Parameters.prototype.getN = function () { return this.n; };
	ec.X9Parameters.prototype.getH = function () { return this.h; };

	// secp256k1 is the Curve used by Bitcoin
	ec.secNamedCurves = {
		// used by Bitcoin
		"secp256k1": function () {
			// p = 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
			var p = ec.fromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F");
			var a = BigInteger.ZERO;
			var b = ec.fromHex("7");
			var n = ec.fromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");
			var h = BigInteger.ONE;
			var curve = new ec.CurveFp(p, a, b);
			var G = curve.decodePointHex("04"
					+ "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"
					+ "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8");
			return new ec.X9Parameters(curve, G, n, h);
		}
	};

	// secp256k1 called by Bitcoin's ECKEY
	ec.getSECCurveByName = function (name) {
		if (ec.secNamedCurves[name] == undefined) return null;
		return ec.secNamedCurves[name]();
	}
})();
 //next 


//start 

 /*
 Coinjs 0.01 beta by OutCast3k{at}gmail.com
 A bitcoin framework.

 http://github.com/OutCast3k/coinjs or http://coinb.in/coinjs
*/

(function () {

	var coinjs = window.coinjs = function () { };

	/* public vars */
	coinjs.pub = 0x00;
	coinjs.priv = 0x80;
	coinjs.multisig = 0x05;
	coinjs.hdkey = {'prv':0x0488ade4, 'pub':0x0488b21e};
	coinjs.bech32 = {'charset':'qpzry9x8gf2tvdw0s3jn54khce6mua7l', 'version':0, 'hrp':'bc'};

	coinjs.compressed = false;

	/* other vars */
	coinjs.developer = '33tht1bKDgZVxb39MnZsWa8oxHXHvUYE4G'; //bitcoin

	/* bit(coinb.in) api vars */
	coinjs.hostname	= ((document.location.hostname.split(".")[(document.location.hostname.split(".")).length-1]) == 'onion') ? '4zpinp6gdkjfplhk.onion' : 'accesscoinx.com';
	coinjs.host = ('https:'==document.location.protocol?'https://':'http://')+coinjs.hostname+'/api/';
	coinjs.uid = '1';
	coinjs.key = '12345678901234567890123456789012';

	/* start of address functions */

	/* generate a private and public keypair, with address and WIF address */
	coinjs.newKeys = function(input){
		var privkey = (input) ? Crypto.SHA256(input) : this.newPrivkey();
		var pubkey = this.newPubkey(privkey);
		return {
			'privkey': privkey,
			'pubkey': pubkey,
			'address': this.pubkey2address(pubkey),
			'wif': this.privkey2wif(privkey),
			'compressed': this.compressed
		};
	}

	/* generate a new random private key */
	coinjs.newPrivkey = function(){
		var x = window.location;
		x += (window.screen.height * window.screen.width * window.screen.colorDepth);
		x += coinjs.random(64);
		x += (window.screen.availHeight * window.screen.availWidth * window.screen.pixelDepth);
		x += navigator.language;
		x += window.history.length;
		x += coinjs.random(64);
		x += navigator.userAgent;
		x += 'coinb.in';
		x += (Crypto.util.randomBytes(64)).join("");
		x += x.length;
		var dateObj = new Date();
		x += dateObj.getTimezoneOffset();
		x += coinjs.random(64);
		x += (document.getElementById("entropybucket")) ? document.getElementById("entropybucket").innerHTML : '';
		x += x+''+x;
		var r = x;
		for(i=0;i<(x).length/25;i++){
			r = Crypto.SHA256(r.concat(x));
		}
		var checkrBigInt = new BigInteger(r);
		var orderBigInt = new BigInteger("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
		while (checkrBigInt.compareTo(orderBigInt) >= 0 || checkrBigInt.equals(BigInteger.ZERO) || checkrBigInt.equals(BigInteger.ONE)) {
			r = Crypto.SHA256(r.concat(x));
			checkrBigInt = new BigInteger(r);
		}
		return r;
	}

	/* generate a public key from a private key */
	coinjs.newPubkey = function(hash){
		var privateKeyBigInt = BigInteger.fromByteArrayUnsigned(Crypto.util.hexToBytes(hash));
		var curve = EllipticCurve.getSECCurveByName("secp256k1");

		var curvePt = curve.getG().multiply(privateKeyBigInt);
		var x = curvePt.getX().toBigInteger();
		var y = curvePt.getY().toBigInteger();

		var publicKeyBytes = EllipticCurve.integerToBytes(x, 32);
		publicKeyBytes = publicKeyBytes.concat(EllipticCurve.integerToBytes(y,32));
		publicKeyBytes.unshift(0x04);

		if(coinjs.compressed==true){
			var publicKeyBytesCompressed = EllipticCurve.integerToBytes(x,32)
			if (y.isEven()){
				publicKeyBytesCompressed.unshift(0x02)
			} else {
				publicKeyBytesCompressed.unshift(0x03)
			}
			return Crypto.util.bytesToHex(publicKeyBytesCompressed);
		} else {
			return Crypto.util.bytesToHex(publicKeyBytes);
		}
	}

	/* provide a public key and return address */
	coinjs.pubkey2address = function(h, byte){
		var r = ripemd160(Crypto.SHA256(Crypto.util.hexToBytes(h), {asBytes: true}));
		r.unshift(byte || coinjs.pub);
		var hash = Crypto.SHA256(Crypto.SHA256(r, {asBytes: true}), {asBytes: true});
		var checksum = hash.slice(0, 4);
		return coinjs.base58encode(r.concat(checksum));
	}

	/* provide a scripthash and return address */
	coinjs.scripthash2address = function(h){
		var x = Crypto.util.hexToBytes(h);
		x.unshift(coinjs.pub);
		var r = x;
		r = Crypto.SHA256(Crypto.SHA256(r,{asBytes: true}),{asBytes: true});
		var checksum = r.slice(0,4);
		return coinjs.base58encode(x.concat(checksum));
	}

	/* new multisig address, provide the pubkeys AND required signatures to release the funds */
	coinjs.pubkeys2MultisigAddress = function(pubkeys, required) {
		var s = coinjs.script();
		s.writeOp(81 + (required*1) - 1); //OP_1
		for (var i = 0; i < pubkeys.length; ++i) {
			s.writeBytes(Crypto.util.hexToBytes(pubkeys[i]));
		}
		s.writeOp(81 + pubkeys.length - 1); //OP_1 
		s.writeOp(174); //OP_CHECKMULTISIG
		var x = ripemd160(Crypto.SHA256(s.buffer, {asBytes: true}), {asBytes: true});
		x.unshift(coinjs.multisig);
		var r = x;
		r = Crypto.SHA256(Crypto.SHA256(r, {asBytes: true}), {asBytes: true});
		var checksum = r.slice(0,4);
		var redeemScript = Crypto.util.bytesToHex(s.buffer);
		var address = coinjs.base58encode(x.concat(checksum));

		if(s.buffer.length > 520){ // too large
			address = 'invalid';
			redeemScript = 'invalid';
		}

		return {'address':address, 'redeemScript':redeemScript, 'size': s.buffer.length};
	}

	/* new time locked address, provide the pubkey and time necessary to unlock the funds.
	   when time is greater than 500000000, it should be a unix timestamp (seconds since epoch),
	   otherwise it should be the block height required before this transaction can be released. 

	   may throw a string on failure!
	*/
	coinjs.simpleHodlAddress = function(pubkey, checklocktimeverify) {

		if(checklocktimeverify < 0) {
			throw "Parameter for OP_CHECKLOCKTIMEVERIFY is negative.";
		}

		var s = coinjs.script();
		if (checklocktimeverify <= 16 && checklocktimeverify >= 1) {
			s.writeOp(0x50 + checklocktimeverify);//OP_1 to OP_16 for minimal encoding
		} else {
			s.writeBytes(coinjs.numToScriptNumBytes(checklocktimeverify));
		}
		s.writeOp(177);//OP_CHECKLOCKTIMEVERIFY
		s.writeOp(117);//OP_DROP
		s.writeBytes(Crypto.util.hexToBytes(pubkey));
		s.writeOp(172);//OP_CHECKSIG

		var x = ripemd160(Crypto.SHA256(s.buffer, {asBytes: true}), {asBytes: true});
		x.unshift(coinjs.multisig);
		var r = x;
		r = Crypto.SHA256(Crypto.SHA256(r, {asBytes: true}), {asBytes: true});
		var checksum = r.slice(0,4);
		var redeemScript = Crypto.util.bytesToHex(s.buffer);
		var address = coinjs.base58encode(x.concat(checksum));

		return {'address':address, 'redeemScript':redeemScript};
	}

	/* create a new segwit address */
	coinjs.segwitAddress = function(pubkey){
		var keyhash = [0x00,0x14].concat(ripemd160(Crypto.SHA256(Crypto.util.hexToBytes(pubkey), {asBytes: true}), {asBytes: true}));
		var x = ripemd160(Crypto.SHA256(keyhash, {asBytes: true}), {asBytes: true});
		x.unshift(coinjs.multisig);
		var r = x;
		r = Crypto.SHA256(Crypto.SHA256(r, {asBytes: true}), {asBytes: true});
		var checksum = r.slice(0,4);
		var address = coinjs.base58encode(x.concat(checksum));

		return {'address':address, 'type':'segwit', 'redeemscript':Crypto.util.bytesToHex(keyhash)};
	}

	/* create a new segwit bech32 encoded address */
	coinjs.bech32Address = function(pubkey){
		var program = ripemd160(Crypto.SHA256(Crypto.util.hexToBytes(pubkey), {asBytes: true}), {asBytes: true});
		var address = coinjs.bech32_encode(coinjs.bech32.hrp, [coinjs.bech32.version].concat(coinjs.bech32_convert(program, 8, 5, true))); 
		return {'address':address, 'type':'bech32', 'redeemscript':Crypto.util.bytesToHex(program)};
	}

	/* extract the redeemscript from a bech32 address */
	coinjs.bech32redeemscript = function(address){
		var r = false;
		var decode = coinjs.bech32_decode(address);
		if(decode){
			decode.data.shift();
			return Crypto.util.bytesToHex(coinjs.bech32_convert(decode.data, 5, 8, false));
		}
		return r;
	}

	/* provide a privkey and return an WIF  */
	coinjs.privkey2wif = function(h){
		var r = Crypto.util.hexToBytes(h);

		if(coinjs.compressed==true){
			r.push(0x01);
		}

		r.unshift(coinjs.priv);
		var hash = Crypto.SHA256(Crypto.SHA256(r, {asBytes: true}), {asBytes: true});
		var checksum = hash.slice(0, 4);

		return coinjs.base58encode(r.concat(checksum));
	}

	/* convert a wif key back to a private key */
	coinjs.wif2privkey = function(wif){
		var compressed = false;
		var decode = coinjs.base58decode(wif);
		var key = decode.slice(0, decode.length-4);
		key = key.slice(1, key.length);
		if(key.length>=33 && key[key.length-1]==0x01){
			key = key.slice(0, key.length-1);
			compressed = true;
		}
		return {'privkey': Crypto.util.bytesToHex(key), 'compressed':compressed};
	}

	/* convert a wif to a pubkey */
	coinjs.wif2pubkey = function(wif){
		var compressed = coinjs.compressed;
		var r = coinjs.wif2privkey(wif);
		coinjs.compressed = r['compressed'];
		var pubkey = coinjs.newPubkey(r['privkey']);
		coinjs.compressed = compressed;
		return {'pubkey':pubkey,'compressed':r['compressed']};
	}

	/* convert a wif to a address */
	coinjs.wif2address = function(wif){
		var r = coinjs.wif2pubkey(wif);
		return {'address':coinjs.pubkey2address(r['pubkey']), 'compressed':r['compressed']};
	}

	/* decode or validate an address and return the hash */
	coinjs.addressDecode = function(addr){
		try {
			var bytes = coinjs.base58decode(addr);
			var front = bytes.slice(0, bytes.length-4);
			var back = bytes.slice(bytes.length-4);
			var checksum = Crypto.SHA256(Crypto.SHA256(front, {asBytes: true}), {asBytes: true}).slice(0, 4);
			if (checksum+"" == back+"") {

				var o = {};
				o.bytes = front.slice(1);
				o.version = front[0];

				if(o.version==coinjs.pub){ // standard address
					o.type = 'standard';

				} else if (o.version==coinjs.multisig) { // multisig address
					o.type = 'multisig';

				} else if (o.version==coinjs.priv){ // wifkey
					o.type = 'wifkey';

				} else if (o.version==42) { // stealth address
					o.type = 'stealth';

					o.option = front[1];
					if (o.option != 0) {
						alert("Stealth Address option other than 0 is currently not supported!");
						return false;
					};

					o.scankey = Crypto.util.bytesToHex(front.slice(2, 35));
					o.n = front[35];

					if (o.n > 1) {
						alert("Stealth Multisig is currently not supported!");
						return false;
					};
				
					o.spendkey = Crypto.util.bytesToHex(front.slice(36, 69));
					o.m = front[69];
					o.prefixlen = front[70];
				
					if (o.prefixlen > 0) {
						alert("Stealth Address Prefixes are currently not supported!");
						return false;
					};
					o.prefix = front.slice(71);

				} else { // everything else
					o.type = 'other'; // address is still valid but unknown version
				}

				return o;
			} else {
				throw "Invalid checksum";
			}
		} catch(e) {
			bech32rs = coinjs.bech32redeemscript(addr);
			if(bech32rs){
				return {'type':'bech32', 'redeemscript':bech32rs};
			} else {
				return false;
			}
		}
	}

	/* retreive the balance from a given address */
	coinjs.addressBalance = function(address, callback){
		coinjs.ajax(coinjs.host+'?uid='+coinjs.uid+'&key='+coinjs.key+'&setmodule=addresses&request=bal&address='+address+'&r='+Math.random(), callback, "GET");
	}

	/* decompress an compressed public key */
	coinjs.pubkeydecompress = function(pubkey) {
		if((typeof(pubkey) == 'string') && pubkey.match(/^[a-f0-9]+$/i)){
			var curve = EllipticCurve.getSECCurveByName("secp256k1");
			try {
				var pt = curve.curve.decodePointHex(pubkey);
				var x = pt.getX().toBigInteger();
				var y = pt.getY().toBigInteger();

				var publicKeyBytes = EllipticCurve.integerToBytes(x, 32);
				publicKeyBytes = publicKeyBytes.concat(EllipticCurve.integerToBytes(y,32));
				publicKeyBytes.unshift(0x04);
				return Crypto.util.bytesToHex(publicKeyBytes);
			} catch (e) {
				// console.log(e);
				return false;
			}
		}
		return false;
	}

	coinjs.bech32_polymod = function(values) {
		var chk = 1;
		var BECH32_GENERATOR = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3];
		for (var p = 0; p < values.length; ++p) {
			var top = chk >> 25;
			chk = (chk & 0x1ffffff) << 5 ^ values[p];
			for (var i = 0; i < 5; ++i) {
				if ((top >> i) & 1) {
					chk ^= BECH32_GENERATOR[i];
				}
			}
		}
		return chk;
	}

	coinjs.bech32_hrpExpand = function(hrp) {
		var ret = [];
		var p;
		for (p = 0; p < hrp.length; ++p) {
			ret.push(hrp.charCodeAt(p) >> 5);
		}
		ret.push(0);
		for (p = 0; p < hrp.length; ++p) {
			ret.push(hrp.charCodeAt(p) & 31);
		}
		return ret;
	}	

	coinjs.	bech32_verifyChecksum = function(hrp, data) {
		return coinjs.bech32_polymod(coinjs.bech32_hrpExpand(hrp).concat(data)) === 1;
	}

	coinjs.bech32_createChecksum = function(hrp, data) {
		var values = coinjs.bech32_hrpExpand(hrp).concat(data).concat([0, 0, 0, 0, 0, 0]);
		var mod = coinjs.bech32_polymod(values) ^ 1;
		var ret = [];
		for (var p = 0; p < 6; ++p) {
			ret.push((mod >> 5 * (5 - p)) & 31);
		}	
		return ret;
	}

	coinjs.bech32_encode = function(hrp, data) {
		var combined = data.concat(coinjs.bech32_createChecksum(hrp, data));
		var ret = hrp + '1';
		for (var p = 0; p < combined.length; ++p) {
			ret += coinjs.bech32.charset.charAt(combined[p]);
		}
		return ret;
	}

	coinjs.bech32_decode = function(bechString) {
		var p;
		var has_lower = false;
		var has_upper = false;
		for (p = 0; p < bechString.length; ++p) {
			if (bechString.charCodeAt(p) < 33 || bechString.charCodeAt(p) > 126) {
				return null;
			}
			if (bechString.charCodeAt(p) >= 97 && bechString.charCodeAt(p) <= 122) {
				has_lower = true;
			}
			if (bechString.charCodeAt(p) >= 65 && bechString.charCodeAt(p) <= 90) {
				has_upper = true;
			}
		}
		if (has_lower && has_upper) {
			return null;
		}
		bechString = bechString.toLowerCase();
		var pos = bechString.lastIndexOf('1');
		if (pos < 1 || pos + 7 > bechString.length || bechString.length > 90) {
			return null;
		}
		var hrp = bechString.substring(0, pos);
		var data = [];
		for (p = pos + 1; p < bechString.length; ++p) {
			var d = coinjs.bech32.charset.indexOf(bechString.charAt(p));
			if (d === -1) {
				return null;
			}
			data.push(d);
		}
		if (!coinjs.bech32_verifyChecksum(hrp, data)) {
			return null;
		}
		return {
			hrp: hrp,
			data: data.slice(0, data.length - 6)
		};
	}

	coinjs.bech32_convert = function(data, inBits, outBits, pad) {
		var value = 0;
		var bits = 0;
		var maxV = (1 << outBits) - 1;

		var result = [];
		for (var i = 0; i < data.length; ++i) {
			value = (value << inBits) | data[i];
			bits += inBits;

			while (bits >= outBits) {
				bits -= outBits;
				result.push((value >> bits) & maxV);
			}
		}

		if (pad) {
			if (bits > 0) {
				result.push((value << (outBits - bits)) & maxV);
			}
		} else {
			if (bits >= inBits) throw new Error('Excess padding');
			if ((value << (outBits - bits)) & maxV) throw new Error('Non-zero padding');
		}

		return result;
	}

	coinjs.testdeterministicK = function() {
		// https://github.com/bitpay/bitcore/blob/9a5193d8e94b0bd5b8e7f00038e7c0b935405a03/test/crypto/ecdsa.js
		// Line 21 and 22 specify digest hash and privkey for the first 2 test vectors.
		// Line 96-117 tells expected result.

		var tx = coinjs.transaction();

		var test_vectors = [
			{
				'message': 'test data',
				'privkey': 'fee0a1f7afebf9d2a5a80c0c98a31c709681cce195cbcd06342b517970c0be1e',
				'k_bad00': 'fcce1de7a9bcd6b2d3defade6afa1913fb9229e3b7ddf4749b55c4848b2a196e',
				'k_bad01': '727fbcb59eb48b1d7d46f95a04991fc512eb9dbf9105628e3aec87428df28fd8',
				'k_bad15': '398f0e2c9f79728f7b3d84d447ac3a86d8b2083c8f234a0ffa9c4043d68bd258'
			},
			{
				'message': 'Everything should be made as simple as possible, but not simpler.',
				'privkey': '0000000000000000000000000000000000000000000000000000000000000001',
				'k_bad00': 'ec633bd56a5774a0940cb97e27a9e4e51dc94af737596a0c5cbb3d30332d92a5',
				'k_bad01': 'df55b6d1b5c48184622b0ead41a0e02bfa5ac3ebdb4c34701454e80aabf36f56',
				'k_bad15': 'def007a9a3c2f7c769c75da9d47f2af84075af95cadd1407393dc1e26086ef87'
			},
			{
				'message': 'Satoshi Nakamoto',
				'privkey': '0000000000000000000000000000000000000000000000000000000000000002',
				'k_bad00': 'd3edc1b8224e953f6ee05c8bbf7ae228f461030e47caf97cde91430b4607405e',
				'k_bad01': 'f86d8e43c09a6a83953f0ab6d0af59fb7446b4660119902e9967067596b58374',
				'k_bad15': '241d1f57d6cfd2f73b1ada7907b199951f95ef5ad362b13aed84009656e0254a'
			},
			{
				'message': 'Diffie Hellman',
				'privkey': '7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f',
				'k_bad00': 'c378a41cb17dce12340788dd3503635f54f894c306d52f6e9bc4b8f18d27afcc',
				'k_bad01': '90756c96fef41152ac9abe08819c4e95f16da2af472880192c69a2b7bac29114',
				'k_bad15': '7b3f53300ab0ccd0f698f4d67db87c44cf3e9e513d9df61137256652b2e94e7c'
			},
			{
				'message': 'Japan',
				'privkey': '8080808080808080808080808080808080808080808080808080808080808080',
				'k_bad00': 'f471e61b51d2d8db78f3dae19d973616f57cdc54caaa81c269394b8c34edcf59',
				'k_bad01': '6819d85b9730acc876fdf59e162bf309e9f63dd35550edf20869d23c2f3e6d17',
				'k_bad15': 'd8e8bae3ee330a198d1f5e00ad7c5f9ed7c24c357c0a004322abca5d9cd17847'
			},
			{
				'message': 'Bitcoin',
				'privkey': 'fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140',
				'k_bad00': '36c848ffb2cbecc5422c33a994955b807665317c1ce2a0f59c689321aaa631cc',
				'k_bad01': '4ed8de1ec952a4f5b3bd79d1ff96446bcd45cabb00fc6ca127183e14671bcb85',
				'k_bad15': '56b6f47babc1662c011d3b1f93aa51a6e9b5f6512e9f2e16821a238d450a31f8'
			},
			{
				'message': 'i2FLPP8WEus5WPjpoHwheXOMSobUJVaZM1JPMQZq',
				'privkey': 'fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140',
				'k_bad00': '6e9b434fcc6bbb081a0463c094356b47d62d7efae7da9c518ed7bac23f4e2ed6',
				'k_bad01': 'ae5323ae338d6117ce8520a43b92eacd2ea1312ae514d53d8e34010154c593bb',
				'k_bad15': '3eaa1b61d1b8ab2f1ca71219c399f2b8b3defa624719f1e96fe3957628c2c4ea'
			},
			{
				'message': 'lEE55EJNP7aLrMtjkeJKKux4Yg0E8E1SAJnWTCEh',
				'privkey': '3881e5286abc580bb6139fe8e83d7c8271c6fe5e5c2d640c1f0ed0e1ee37edc9',
				'k_bad00': '5b606665a16da29cc1c5411d744ab554640479dd8abd3c04ff23bd6b302e7034',
				'k_bad01': 'f8b25263152c042807c992eacd2ac2cc5790d1e9957c394f77ea368e3d9923bd',
				'k_bad15': 'ea624578f7e7964ac1d84adb5b5087dd14f0ee78b49072aa19051cc15dab6f33'
			},
			{
				'message': '2SaVPvhxkAPrayIVKcsoQO5DKA8Uv5X/esZFlf+y',
				'privkey': '7259dff07922de7f9c4c5720d68c9745e230b32508c497dd24cb95ef18856631',
				'k_bad00': '3ab6c19ab5d3aea6aa0c6da37516b1d6e28e3985019b3adb388714e8f536686b',
				'k_bad01': '19af21b05004b0ce9cdca82458a371a9d2cf0dc35a813108c557b551c08eb52e',
				'k_bad15': '117a32665fca1b7137a91c4739ac5719fec0cf2e146f40f8e7c21b45a07ebc6a'
			},
			{
				'message': '00A0OwO2THi7j5Z/jp0FmN6nn7N/DQd6eBnCS+/b',
				'privkey': '0d6ea45d62b334777d6995052965c795a4f8506044b4fd7dc59c15656a28f7aa',
				'k_bad00': '79487de0c8799158294d94c0eb92ee4b567e4dc7ca18addc86e49d31ce1d2db6',
				'k_bad01': '9561d2401164a48a8f600882753b3105ebdd35e2358f4f808c4f549c91490009',
				'k_bad15': 'b0d273634129ff4dbdf0df317d4062a1dbc58818f88878ffdb4ec511c77976c0'
			}
		];

		var result_txt = '\n----------------------\nResults\n----------------------\n\n';

		for (i = 0; i < test_vectors.length; i++) {
			var hash = Crypto.SHA256(test_vectors[i]['message'].split('').map(function (c) { return c.charCodeAt (0); }), { asBytes: true });
			var wif = coinjs.privkey2wif(test_vectors[i]['privkey']);

			var KBigInt = tx.deterministicK(wif, hash);
			var KBigInt0 = tx.deterministicK(wif, hash, 0);
			var KBigInt1 = tx.deterministicK(wif, hash, 1);
			var KBigInt15 = tx.deterministicK(wif, hash, 15);

			var K = Crypto.util.bytesToHex(KBigInt.toByteArrayUnsigned());
			var K0 = Crypto.util.bytesToHex(KBigInt0.toByteArrayUnsigned());
			var K1 = Crypto.util.bytesToHex(KBigInt1.toByteArrayUnsigned());
			var K15 = Crypto.util.bytesToHex(KBigInt15.toByteArrayUnsigned());

			if (K != test_vectors[i]['k_bad00']) {
				result_txt += 'Failed Test #' + (i + 1) + '\n       K = ' + K + '\nExpected = ' + test_vectors[i]['k_bad00'] + '\n\n';
			} else if (K0 != test_vectors[i]['k_bad00']) {
				result_txt += 'Failed Test #' + (i + 1) + '\n      K0 = ' + K0 + '\nExpected = ' + test_vectors[i]['k_bad00'] + '\n\n';
			} else if (K1 != test_vectors[i]['k_bad01']) {
				result_txt += 'Failed Test #' + (i + 1) + '\n      K1 = ' + K1 + '\nExpected = ' + test_vectors[i]['k_bad01'] + '\n\n';
			} else if (K15 != test_vectors[i]['k_bad15']) {
				result_txt += 'Failed Test #' + (i + 1) + '\n     K15 = ' + K15 + '\nExpected = ' + test_vectors[i]['k_bad15'] + '\n\n';
			};
		};

		if (result_txt.length < 60) {
			result_txt = 'All Tests OK!';
		};

		return result_txt;
	};

	/* start of hd functions, thanks bip32.org */
	coinjs.hd = function(data){

		var r = {};

		/* some hd value parsing */
		r.parse = function() {

			var bytes = [];

			// some quick validation
			if(typeof(data) == 'string'){
				var decoded = coinjs.base58decode(data);
				if(decoded.length == 82){
					var checksum = decoded.slice(78, 82);
					var hash = Crypto.SHA256(Crypto.SHA256(decoded.slice(0, 78), { asBytes: true } ), { asBytes: true } );
					if(checksum[0]==hash[0] && checksum[1]==hash[1] && checksum[2]==hash[2] && checksum[3]==hash[3]){
						bytes = decoded.slice(0, 78);
					}
				}
			}

			// actual parsing code
			if(bytes && bytes.length>0) {
 				r.version = coinjs.uint(bytes.slice(0, 4) , 4);
 				r.depth = coinjs.uint(bytes.slice(4, 5) ,1);
				r.parent_fingerprint = bytes.slice(5, 9);
				r.child_index = coinjs.uint(bytes.slice(9, 13), 4);
 				r.chain_code = bytes.slice(13, 45);
				r.key_bytes = bytes.slice(45, 78);

				var c = coinjs.compressed; // get current default
				coinjs.compressed = true;

				if(r.key_bytes[0] == 0x00) {
					r.type = 'private';
					var privkey = (r.key_bytes).slice(1, 33);
					var privkeyHex = Crypto.util.bytesToHex(privkey);
					var pubkey = coinjs.newPubkey(privkeyHex);

					r.keys = {'privkey':privkeyHex,
						'pubkey':pubkey,
						'address':coinjs.pubkey2address(pubkey),
						'wif':coinjs.privkey2wif(privkeyHex)};

				} else if(r.key_bytes[0] == 0x02 || r.key_bytes[0] == 0x03) {
					r.type = 'public';
					var pubkeyHex = Crypto.util.bytesToHex(r.key_bytes);

					r.keys = {'pubkey': pubkeyHex,
						'address':coinjs.pubkey2address(pubkeyHex)};
				} else {
					r.type = 'invalid';
				}

				r.keys_extended = r.extend();

				coinjs.compressed = c; // reset to default
			}

			return r;
		}

		// extend prv/pub key
		r.extend = function(){
			var hd = coinjs.hd();
			return hd.make({'depth':(this.depth*1)+1,
				'parent_fingerprint':this.parent_fingerprint,
				'child_index':this.child_index,
				'chain_code':this.chain_code,
				'privkey':this.keys.privkey,
				'pubkey':this.keys.pubkey});
		}

		// derive from path
		r.derive_path = function(path) {

			if( path == 'm' || path == 'M' || path == 'm\'' || path == 'M\'' ) return this;

			var p = path.split('/');
			var hdp = coinjs.clone(this);  // clone hd path

			for( var i in p ) {

				if((( i == 0 ) && c != 'm') || i == 'remove'){
					continue;
				}

				var c = p[i];

				var use_private = (c.length > 1) && (c[c.length-1] == '\'');
				var child_index = parseInt(use_private ? c.slice(0, c.length - 1) : c) & 0x7fffffff;
				if(use_private)
					child_index += 0x80000000;

				hdp = hdp.derive(child_index);
				var key = ((hdp.keys_extended.privkey) && hdp.keys_extended.privkey!='') ? hdp.keys_extended.privkey : hdp.keys_extended.pubkey;
				hdp = coinjs.hd(key);
			}
			return hdp;
		}

		// derive key from index
		r.derive = function(i){

			i = (i)?i:0;
			var blob = (Crypto.util.hexToBytes(this.keys.pubkey)).concat(coinjs.numToBytes(i,4).reverse());

			var j = new jsSHA(Crypto.util.bytesToHex(blob), 'HEX');
 			var hash = j.getHMAC(Crypto.util.bytesToHex(r.chain_code), "HEX", "SHA-512", "HEX");

			var il = new BigInteger(hash.slice(0, 64), 16);
			var ir = Crypto.util.hexToBytes(hash.slice(64,128));

			var ecparams = EllipticCurve.getSECCurveByName("secp256k1");
			var curve = ecparams.getCurve();

			var k, key, pubkey, o;

			o = coinjs.clone(this);
			o.chain_code = ir;
			o.child_index = i;

			if(this.type=='private'){
				// derive key pair from from a xprv key
				k = il.add(new BigInteger([0].concat(Crypto.util.hexToBytes(this.keys.privkey)))).mod(ecparams.getN());
				key = Crypto.util.bytesToHex(k.toByteArrayUnsigned());

				pubkey = coinjs.newPubkey(key);

				o.keys = {'privkey':key,
					'pubkey':pubkey,
					'wif':coinjs.privkey2wif(key),
					'address':coinjs.pubkey2address(pubkey)};

			} else if (this.type=='public'){
				// derive xpub key from an xpub key
				q = ecparams.curve.decodePointHex(this.keys.pubkey);
				var curvePt = ecparams.getG().multiply(il).add(q);

				var x = curvePt.getX().toBigInteger();
				var y = curvePt.getY().toBigInteger();

				var publicKeyBytesCompressed = EllipticCurve.integerToBytes(x,32)
				if (y.isEven()){
					publicKeyBytesCompressed.unshift(0x02)
				} else {
					publicKeyBytesCompressed.unshift(0x03)
				}
				pubkey = Crypto.util.bytesToHex(publicKeyBytesCompressed);

				o.keys = {'pubkey':pubkey,
					'address':coinjs.pubkey2address(pubkey)}
			} else {
				// fail
			}

			o.parent_fingerprint = (ripemd160(Crypto.SHA256(Crypto.util.hexToBytes(r.keys.pubkey),{asBytes:true}),{asBytes:true})).slice(0,4);
			o.keys_extended = o.extend();
			return o;
		}

		// make a master hd xprv/xpub
		r.master = function(pass) {
			var seed = (pass) ? Crypto.SHA256(pass) : coinjs.newPrivkey();
			var hasher = new jsSHA(seed, 'HEX');
			var I = hasher.getHMAC("Bitcoin seed", "TEXT", "SHA-512", "HEX");

			var privkey = Crypto.util.hexToBytes(I.slice(0, 64));
			var chain = Crypto.util.hexToBytes(I.slice(64, 128));

			var hd = coinjs.hd();
			return hd.make({'depth':0,
				'parent_fingerprint':[0,0,0,0],
				'child_index':0,
				'chain_code':chain,
				'privkey':I.slice(0, 64),
				'pubkey':coinjs.newPubkey(I.slice(0, 64))});
		}

		// encode data to a base58 string
		r.make = function(data){ // { (int) depth, (array) parent_fingerprint, (int) child_index, (byte array) chain_code, (hex str) privkey, (hex str) pubkey}
			var k = [];

			//depth
			k.push(data.depth*1);

			//parent fingerprint
			k = k.concat(data.parent_fingerprint);

			//child index
			k = k.concat((coinjs.numToBytes(data.child_index, 4)).reverse());

			//Chain code
			k = k.concat(data.chain_code);

			var o = {}; // results

			//encode xprv key
			if(data.privkey){
				var prv = (coinjs.numToBytes(coinjs.hdkey.prv, 4)).reverse();
				prv = prv.concat(k);
				prv.push(0x00);
				prv = prv.concat(Crypto.util.hexToBytes(data.privkey));
				var hash = Crypto.SHA256( Crypto.SHA256(prv, { asBytes: true } ), { asBytes: true } );
				var checksum = hash.slice(0, 4);
				var ret = prv.concat(checksum);
				o.privkey = coinjs.base58encode(ret);
			}

			//encode xpub key
			if(data.pubkey){
				var pub = (coinjs.numToBytes(coinjs.hdkey.pub, 4)).reverse();
				pub = pub.concat(k);
				pub = pub.concat(Crypto.util.hexToBytes(data.pubkey));
				var hash = Crypto.SHA256( Crypto.SHA256(pub, { asBytes: true } ), { asBytes: true } );
				var checksum = hash.slice(0, 4);
				var ret = pub.concat(checksum);
				o.pubkey = coinjs.base58encode(ret);
			}
			return o;
		}

		return r.parse();
	}


	/* start of script functions */
	coinjs.script = function(data) {
		var r = {};

		if(!data){
			r.buffer = [];
		} else if ("string" == typeof data) {
			r.buffer = Crypto.util.hexToBytes(data);
		} else if (coinjs.isArray(data)) {
			r.buffer = data;
		} else if (data instanceof coinjs.script) {
			r.buffer = data.buffer;
		} else {
			r.buffer = data;
		}

		/* parse buffer array */
		r.parse = function () {

			var self = this;
			r.chunks = [];
			var i = 0;

			function readChunk(n) {
				self.chunks.push(self.buffer.slice(i, i + n));
				i += n;
			};

			while (i < this.buffer.length) {
				var opcode = this.buffer[i++];
				if (opcode >= 0xF0) {
 					opcode = (opcode << 8) | this.buffer[i++];
				}

				var len;
				if (opcode > 0 && opcode < 76) { //OP_PUSHDATA1
					readChunk(opcode);
				} else if (opcode == 76) { //OP_PUSHDATA1
					len = this.buffer[i++];
					readChunk(len);
				} else if (opcode == 77) { //OP_PUSHDATA2
 					len = (this.buffer[i++] << 8) | this.buffer[i++];
					readChunk(len);
				} else if (opcode == 78) { //OP_PUSHDATA4
					len = (this.buffer[i++] << 24) | (this.buffer[i++] << 16) | (this.buffer[i++] << 8) | this.buffer[i++];
					readChunk(len);
				} else {
					this.chunks.push(opcode);
				}

				if(i<0x00){
					break;
				}
			}

			return true;
		};

		/* decode the redeemscript of a multisignature transaction */
		r.decodeRedeemScript = function(script){
			var r = false;
			try {
				var s = coinjs.script(Crypto.util.hexToBytes(script));
				if((s.chunks.length>=3) && s.chunks[s.chunks.length-1] == 174){//OP_CHECKMULTISIG
					r = {};
					r.signaturesRequired = s.chunks[0]-80;
					var pubkeys = [];
					for(var i=1;i<s.chunks.length-2;i++){
						pubkeys.push(Crypto.util.bytesToHex(s.chunks[i]));
					}
					r.pubkeys = pubkeys;
					var multi = coinjs.pubkeys2MultisigAddress(pubkeys, r.signaturesRequired);
					r.address = multi['address'];
					r.type = 'multisig__'; // using __ for now to differentiat from the other object .type == "multisig"
					var rs = Crypto.util.bytesToHex(s.buffer);
					r.redeemscript = rs;

				} else if((s.chunks.length==2) && (s.buffer[0] == 0 && s.buffer[1] == 20)){ // SEGWIT
					r = {};
					r.type = "segwit__";
					var rs = Crypto.util.bytesToHex(s.buffer);
					r.address = coinjs.pubkey2address(rs, coinjs.multisig);
					r.redeemscript = rs;

				} else if(s.chunks.length == 5 && s.chunks[1] == 177 && s.chunks[2] == 117 && s.chunks[4] == 172){
					// ^ <unlocktime> OP_CHECKLOCKTIMEVERIFY OP_DROP <pubkey> OP_CHECKSIG ^
					r = {}
					r.pubkey = Crypto.util.bytesToHex(s.chunks[3]);
					r.checklocktimeverify = coinjs.bytesToNum(s.chunks[0].slice());
					r.address = coinjs.simpleHodlAddress(r.pubkey, r.checklocktimeverify).address;
					var rs = Crypto.util.bytesToHex(s.buffer);
					r.redeemscript = rs;
					r.type = "hodl__";
				}
			} catch(e) {
				// console.log(e);
				r = false;
			}
			return r;
		}

		/* create output script to spend */
		r.spendToScript = function(address){
			var addr = coinjs.addressDecode(address);
			var s = coinjs.script();
			if(addr.type == "bech32"){
				s.writeOp(0);
				s.writeBytes(Crypto.util.hexToBytes(addr.redeemscript));
			} else if(addr.version==coinjs.multisig){ // multisig address
				s.writeOp(169); //OP_HASH160
				s.writeBytes(addr.bytes);
				s.writeOp(135); //OP_EQUAL
			} else { // regular address
				s.writeOp(118); //OP_DUP
				s.writeOp(169); //OP_HASH160
				s.writeBytes(addr.bytes);
				s.writeOp(136); //OP_EQUALVERIFY
				s.writeOp(172); //OP_CHECKSIG
			}
			return s;
		}

		/* geneate a (script) pubkey hash of the address - used for when signing */
		r.pubkeyHash = function(address) {
			var addr = coinjs.addressDecode(address);
			var s = coinjs.script();
			s.writeOp(118);//OP_DUP
			s.writeOp(169);//OP_HASH160
			s.writeBytes(addr.bytes);
			s.writeOp(136);//OP_EQUALVERIFY
			s.writeOp(172);//OP_CHECKSIG
			return s;
		}

		/* write to buffer */
		r.writeOp = function(op){
			this.buffer.push(op);
			this.chunks.push(op);
			return true;
		}

		/* write bytes to buffer */
		r.writeBytes = function(data){
			if (data.length < 76) {	//OP_PUSHDATA1
				this.buffer.push(data.length);
			} else if (data.length <= 0xff) {
				this.buffer.push(76); //OP_PUSHDATA1
				this.buffer.push(data.length);
			} else if (data.length <= 0xffff) {
				this.buffer.push(77); //OP_PUSHDATA2
				this.buffer.push(data.length & 0xff);
				this.buffer.push((data.length >>> 8) & 0xff);
			} else {
				this.buffer.push(78); //OP_PUSHDATA4
				this.buffer.push(data.length & 0xff);
				this.buffer.push((data.length >>> 8) & 0xff);
				this.buffer.push((data.length >>> 16) & 0xff);
				this.buffer.push((data.length >>> 24) & 0xff);
			}
			this.buffer = this.buffer.concat(data);
			this.chunks.push(data);
			return true;
		}

		r.parse();
		return r;
	}

	/* start of transaction functions */

	/* create a new transaction object */
	coinjs.transaction = function() {

		var r = {};
		r.version = 1;
		r.lock_time = 0;
		r.ins = [];
		r.outs = [];
		r.witness = false;
		r.timestamp = null;
		r.block = null;

		/* add an input to a transaction */
		r.addinput = function(txid, index, script, sequence){
			var o = {};
			o.outpoint = {'hash':txid, 'index':index};
			o.script = coinjs.script(script||[]);
			o.sequence = sequence || ((r.lock_time==0) ? 4294967295 : 0);
			return this.ins.push(o);
		}

		/* add an output to a transaction */
		r.addoutput = function(address, value){
			var o = {};
			o.value = new BigInteger('' + Math.round((value*1) * 1e8), 10);
			var s = coinjs.script();
			o.script = s.spendToScript(address);

			return this.outs.push(o);
		}

		/* add two outputs for stealth addresses to a transaction */
		r.addstealth = function(stealth, value){
			var ephemeralKeyBigInt = BigInteger.fromByteArrayUnsigned(Crypto.util.hexToBytes(coinjs.newPrivkey()));
			var curve = EllipticCurve.getSECCurveByName("secp256k1");
			
			var p = EllipticCurve.fromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F");
			var a = BigInteger.ZERO;
			var b = EllipticCurve.fromHex("7");
			var calccurve = new EllipticCurve.CurveFp(p, a, b);
			
			var ephemeralPt = curve.getG().multiply(ephemeralKeyBigInt);
			var scanPt = calccurve.decodePointHex(stealth.scankey);
			var sharedPt = scanPt.multiply(ephemeralKeyBigInt);
			var stealthindexKeyBigInt = BigInteger.fromByteArrayUnsigned(Crypto.SHA256(sharedPt.getEncoded(true), {asBytes: true}));
			
			var stealthindexPt = curve.getG().multiply(stealthindexKeyBigInt);
			var spendPt = calccurve.decodePointHex(stealth.spendkey);
			var addressPt = spendPt.add(stealthindexPt);
			
			var sendaddress = coinjs.pubkey2address(Crypto.util.bytesToHex(addressPt.getEncoded(true)));
			
			
			var OPRETBytes = [6].concat(Crypto.util.randomBytes(4)).concat(ephemeralPt.getEncoded(true)); // ephemkey data
			var q = coinjs.script();
			q.writeOp(106); // OP_RETURN
			q.writeBytes(OPRETBytes);
			v = {};
			v.value = 0;
			v.script = q;
			
			this.outs.push(v);
			
			var o = {};
			o.value = new BigInteger('' + Math.round((value*1) * 1e8), 10);
			var s = coinjs.script();
			o.script = s.spendToScript(sendaddress);
			
			return this.outs.push(o);
		}

		/* add data to a transaction */
		r.adddata = function(data){
			var r = false;
			if(((data.match(/^[a-f0-9]+$/gi)) && data.length<160) && (data.length%2)==0) {
				var s = coinjs.script();
				s.writeOp(106); // OP_RETURN
				s.writeBytes(Crypto.util.hexToBytes(data));
				o = {};
				o.value = 0;
				o.script = s;
				return this.outs.push(o);
			}
			return r;
		}

		/* list unspent transactions */
		r.listUnspent = function(address, callback) {
			coinjs.ajax(coinjs.host+'?uid='+coinjs.uid+'&key='+coinjs.key+'&setmodule=addresses&request=unspent&address='+address+'&r='+Math.random(), callback, "GET");
		}

		/* list transaction data */
		r.getTransaction = function(txid, callback) {
			coinjs.ajax(coinjs.host+'?uid='+coinjs.uid+'&key='+coinjs.key+'&setmodule=bitcoin&request=gettransaction&txid='+txid+'&r='+Math.random(), callback, "GET");
		}

		/* add unspent to transaction */
		r.addUnspent = function(address, callback, script, segwit, sequence){
			var self = this;
			this.listUnspent(address, function(data){
				var s = coinjs.script();
				var value = 0;
				var total = 0;
				var x = {};

				if (window.DOMParser) {
					parser=new DOMParser();
					xmlDoc=parser.parseFromString(data,"text/xml");
				} else {
					xmlDoc=new ActiveXObject("Microsoft.XMLDOM");
					xmlDoc.async=false;
					xmlDoc.loadXML(data);
				}

				var unspent = xmlDoc.getElementsByTagName("unspent")[0];

				if(unspent){ 
					for(i=1;i<=unspent.childElementCount;i++){
						var u = xmlDoc.getElementsByTagName("unspent_"+i)[0]
						var txhash = (u.getElementsByTagName("tx_hash")[0].childNodes[0].nodeValue).match(/.{1,2}/g).reverse().join("")+'';
						var n = u.getElementsByTagName("tx_output_n")[0].childNodes[0].nodeValue;
						var scr = script || u.getElementsByTagName("script")[0].childNodes[0].nodeValue;

						if(segwit){
							/* this is a small hack to include the value with the redeemscript to make the signing procedure smoother. 
							It is not standard and removed during the signing procedure. */

							s = coinjs.script();
							s.writeBytes(Crypto.util.hexToBytes(script));
							s.writeOp(0);
							s.writeBytes(coinjs.numToBytes(u.getElementsByTagName("value")[0].childNodes[0].nodeValue*1, 8));
							scr = Crypto.util.bytesToHex(s.buffer);
						}

						var seq = sequence || false;
						self.addinput(txhash, n, scr, seq);
						value += u.getElementsByTagName("value")[0].childNodes[0].nodeValue*1;
						total++;
					}
				}

				x.result = xmlDoc.getElementsByTagName("result")[0].childNodes[0].nodeValue;
				x.unspent = unspent;
				x.value = value;
				x.total = total;
				x.response = xmlDoc.getElementsByTagName("response")[0].childNodes[0].nodeValue;

				return callback(x);
			});
		}

		/* add unspent and sign */
		r.addUnspentAndSign = function(wif, callback){
			var self = this;
			var address = coinjs.wif2address(wif);
			self.addUnspent(address['address'], function(data){
				self.sign(wif);
				return callback(data);
			});
		}

		/* broadcast a transaction */
		r.broadcast = function(callback, txhex){
			var tx = txhex || this.serialize();
			coinjs.ajax(coinjs.host+'?uid='+coinjs.uid+'&key='+coinjs.key+'&setmodule=bitcoin&request=sendrawtransaction&rawtx='+tx+'&r='+Math.random(), callback, "GET");
		}

		/* generate the transaction hash to sign from a transaction input */
		r.transactionHash = function(index, sigHashType) {

			var clone = coinjs.clone(this);
			var shType = sigHashType || 1;

			/* black out all other ins, except this one */
			for (var i = 0; i < clone.ins.length; i++) {
				if(index!=i){
					clone.ins[i].script = coinjs.script();
				}
			}

			var extract = this.extractScriptKey(index);
			clone.ins[index].script = coinjs.script(extract['script']);

			if((clone.ins) && clone.ins[index]){

				/* SIGHASH : For more info on sig hashs see https://en.bitcoin.it/wiki/OP_CHECKSIG
					and https://bitcoin.org/en/developer-guide#signature-hash-type */

				if(shType == 1){
					//SIGHASH_ALL 0x01

				} else if(shType == 2){
					//SIGHASH_NONE 0x02
					clone.outs = [];
					for (var i = 0; i < clone.ins.length; i++) {
						if(index!=i){
							clone.ins[i].sequence = 0;
						}
					}

				} else if(shType == 3){

					//SIGHASH_SINGLE 0x03
					clone.outs.length = index + 1;

					for(var i = 0; i < index; i++){
						clone.outs[i].value = -1;
						clone.outs[i].script.buffer = [];
					}

					for (var i = 0; i < clone.ins.length; i++) {
						if(index!=i){
							clone.ins[i].sequence = 0;
						}
					}

				} else if (shType >= 128){
					//SIGHASH_ANYONECANPAY 0x80
					clone.ins = [clone.ins[index]];

					if(shType==129){
						// SIGHASH_ALL + SIGHASH_ANYONECANPAY

					} else if(shType==130){
						// SIGHASH_NONE + SIGHASH_ANYONECANPAY
						clone.outs = [];

					} else if(shType==131){
                                                // SIGHASH_SINGLE + SIGHASH_ANYONECANPAY
						clone.outs.length = index + 1;
						for(var i = 0; i < index; i++){
							clone.outs[i].value = -1;
							clone.outs[i].script.buffer = [];
						}
					}
				}

				var buffer = Crypto.util.hexToBytes(clone.serialize());
				buffer = buffer.concat(coinjs.numToBytes(parseInt(shType), 4));
				var hash = Crypto.SHA256(buffer, {asBytes: true});
				var r = Crypto.util.bytesToHex(Crypto.SHA256(hash, {asBytes: true}));
				return r;
			} else {
				return false;
			}
		}

		/* generate a segwit transaction hash to sign from a transaction input */
		r.transactionHashSegWitV0 = function(index, sigHashType){
			/* 
			   Notice: coinb.in by default, deals with segwit transactions in a non-standard way.
			   Segwit transactions require that input values are included in the transaction hash.
			   To save wasting resources and potentially slowing down this service, we include the amount with the 
			   redeem script to generate the transaction hash and remove it after its signed.
			*/

			// start redeem script check
			var extract = this.extractScriptKey(index);
			if(extract['type'] != 'segwit'){
				return {'result':0, 'fail':'redeemscript', 'response':'redeemscript missing or not valid for segwit'};
			}

			if(extract['value'] == -1){
				return {'result':0, 'fail':'value', 'response':'unable to generate a valid segwit hash without a value'};				
			}

			var scriptcode = Crypto.util.hexToBytes(extract['script']);

			// end of redeem script check

			/* P2WPKH */
			if(scriptcode.length == 20){
				scriptcode = [0x00,0x14].concat(scriptcode);
			}

			if(scriptcode.length == 22){
				scriptcode = scriptcode.slice(1);
				scriptcode.unshift(25, 118, 169);
				scriptcode.push(136, 172);
			}

			var value = coinjs.numToBytes(extract['value'], 8);

			// start

			var zero = coinjs.numToBytes(0, 32);
			var version = coinjs.numToBytes(parseInt(this.version), 4);

			var bufferTmp = [];
			if(!(sigHashType >= 80)){	// not sighash anyonecanpay 
				for(var i = 0; i < this.ins.length; i++){
					bufferTmp = bufferTmp.concat(Crypto.util.hexToBytes(this.ins[i].outpoint.hash).reverse());
					bufferTmp = bufferTmp.concat(coinjs.numToBytes(this.ins[i].outpoint.index, 4));
				}
			}
			var hashPrevouts = bufferTmp.length >= 1 ? Crypto.SHA256(Crypto.SHA256(bufferTmp, {asBytes: true}), {asBytes: true}) : zero; 

			var bufferTmp = [];
			if(!(sigHashType >= 80) && sigHashType != 2 && sigHashType != 3){ // not sighash anyonecanpay & single & none
				for(var i = 0; i < this.ins.length; i++){
					bufferTmp = bufferTmp.concat(coinjs.numToBytes(this.ins[i].sequence, 4));
				}
			}
			var hashSequence = bufferTmp.length >= 1 ? Crypto.SHA256(Crypto.SHA256(bufferTmp, {asBytes: true}), {asBytes: true}) : zero; 

			var outpoint = Crypto.util.hexToBytes(this.ins[index].outpoint.hash).reverse();
			outpoint = outpoint.concat(coinjs.numToBytes(this.ins[index].outpoint.index, 4));

			var nsequence = coinjs.numToBytes(this.ins[index].sequence, 4);
			var hashOutputs = zero;
			var bufferTmp = [];
			if(sigHashType != 2 && sigHashType != 3){		// not sighash single & none
				for(var i = 0; i < this.outs.length; i++ ){
					bufferTmp = bufferTmp.concat(coinjs.numToBytes(this.outs[i].value, 8));
					bufferTmp = bufferTmp.concat(coinjs.numToVarInt(this.outs[i].script.buffer.length));
					bufferTmp = bufferTmp.concat(this.outs[i].script.buffer);
				}
				hashOutputs = Crypto.SHA256(Crypto.SHA256(bufferTmp, {asBytes: true}), {asBytes: true});

			} else if ((sigHashType == 2) && index < this.outs.length){ // is sighash single
				bufferTmp = bufferTmp.concat(coinjs.numToBytes(this.outs[index].value, 8));
				bufferTmp = bufferTmp.concat(coinjs.numToVarInt(this.outs[i].script.buffer.length));
				bufferTmp = bufferTmp.concat(this.outs[index].script.buffer);
				hashOutputs = Crypto.SHA256(Crypto.SHA256(bufferTmp, {asBytes: true}), {asBytes: true});
			}

			var locktime = coinjs.numToBytes(this.lock_time, 4);
			var sighash = coinjs.numToBytes(sigHashType, 4);

			var buffer = []; 
			buffer = buffer.concat(version);
			buffer = buffer.concat(hashPrevouts);
			buffer = buffer.concat(hashSequence);
			buffer = buffer.concat(outpoint);
			buffer = buffer.concat(scriptcode);
			buffer = buffer.concat(value);
			buffer = buffer.concat(nsequence);
			buffer = buffer.concat(hashOutputs);
			buffer = buffer.concat(locktime);
			buffer = buffer.concat(sighash);

			var hash = Crypto.SHA256(buffer, {asBytes: true});
			return {'result':1,'hash':Crypto.util.bytesToHex(Crypto.SHA256(hash, {asBytes: true})), 'response':'hash generated'};
		}

		/* extract the scriptSig, used in the transactionHash() function */
		r.extractScriptKey = function(index) {
			if(this.ins[index]){
				if((this.ins[index].script.chunks.length==5) && this.ins[index].script.chunks[4]==172 && coinjs.isArray(this.ins[index].script.chunks[2])){ //OP_CHECKSIG
					// regular scriptPubkey (not signed)
					return {'type':'scriptpubkey', 'signed':'false', 'signatures':0, 'script': Crypto.util.bytesToHex(this.ins[index].script.buffer)};
				} else if((this.ins[index].script.chunks.length==2) && this.ins[index].script.chunks[0][0]==48 && this.ins[index].script.chunks[1].length == 5 && this.ins[index].script.chunks[1][1]==177){//OP_CHECKLOCKTIMEVERIFY
					// hodl script (signed)
					return {'type':'hodl', 'signed':'true', 'signatures':1, 'script': Crypto.util.bytesToHex(this.ins[index].script.buffer)};
				} else if((this.ins[index].script.chunks.length==2) && this.ins[index].script.chunks[0][0]==48){ 
					// regular scriptPubkey (probably signed)
					return {'type':'scriptpubkey', 'signed':'true', 'signatures':1, 'script': Crypto.util.bytesToHex(this.ins[index].script.buffer)};
				} else if(this.ins[index].script.chunks.length == 5 && this.ins[index].script.chunks[1] == 177){//OP_CHECKLOCKTIMEVERIFY
					// hodl script (not signed)
					return {'type':'hodl', 'signed':'false', 'signatures': 0, 'script': Crypto.util.bytesToHex(this.ins[index].script.buffer)};
				} else if((this.ins[index].script.chunks.length <= 3 && this.ins[index].script.chunks.length > 0) && ((this.ins[index].script.chunks[0].length == 22 && this.ins[index].script.chunks[0][0] == 0) || (this.ins[index].script.chunks[0].length == 20 && this.ins[index].script.chunks[1] == 0))){
					var signed = ((this.witness[index]) && this.witness[index].length==2) ? 'true' : 'false';
					var sigs = (signed == 'true') ? 1 : 0;
					var value = -1; // no value found
					if((this.ins[index].script.chunks[2]) && this.ins[index].script.chunks[2].length==8){
						value = coinjs.bytesToNum(this.ins[index].script.chunks[2]);  // value found encoded in transaction (THIS IS NON STANDARD)
					}
					return {'type':'segwit', 'signed':signed, 'signatures': sigs, 'script': Crypto.util.bytesToHex(this.ins[index].script.chunks[0]), 'value': value};
				} else if (this.ins[index].script.chunks[0]==0 && this.ins[index].script.chunks[this.ins[index].script.chunks.length-1][this.ins[index].script.chunks[this.ins[index].script.chunks.length-1].length-1]==174) { // OP_CHECKMULTISIG
					// multisig script, with signature(s) included
					sigcount = 0;
					for(i=1; i<this.ins[index].script.chunks.length-1;i++){
						if(this.ins[index].script.chunks[i]!=0){
							sigcount++;
						}
					}

					return {'type':'multisig', 'signed':'true', 'signatures':sigcount, 'script': Crypto.util.bytesToHex(this.ins[index].script.chunks[this.ins[index].script.chunks.length-1])};
				} else if (this.ins[index].script.chunks[0]>=80 && this.ins[index].script.chunks[this.ins[index].script.chunks.length-1]==174) { // OP_CHECKMULTISIG
					// multisig script, without signature!
					return {'type':'multisig', 'signed':'false', 'signatures':0, 'script': Crypto.util.bytesToHex(this.ins[index].script.buffer)};
				} else if (this.ins[index].script.chunks.length==0) {
					// empty
					return {'type':'empty', 'signed':'false', 'signatures':0, 'script': ''};
				} else {
					// something else
					return {'type':'unknown', 'signed':'false', 'signatures':0, 'script':Crypto.util.bytesToHex(this.ins[index].script.buffer)};
				}
			} else {
				return false;
			}
		}

		/* generate a signature from a transaction hash */
		r.transactionSig = function(index, wif, sigHashType, txhash){

			function serializeSig(r, s) {
				var rBa = r.toByteArraySigned();
				var sBa = s.toByteArraySigned();

				var sequence = [];
				sequence.push(0x02); // INTEGER
				sequence.push(rBa.length);
				sequence = sequence.concat(rBa);

				sequence.push(0x02); // INTEGER
				sequence.push(sBa.length);
				sequence = sequence.concat(sBa);

				sequence.unshift(sequence.length);
				sequence.unshift(0x30); // SEQUENCE

				return sequence;
			}

			var shType = sigHashType || 1;
			var hash = txhash || Crypto.util.hexToBytes(this.transactionHash(index, shType));

			if(hash){
				var curve = EllipticCurve.getSECCurveByName("secp256k1");
				var key = coinjs.wif2privkey(wif);
				var priv = BigInteger.fromByteArrayUnsigned(Crypto.util.hexToBytes(key['privkey']));
				var n = curve.getN();
				var e = BigInteger.fromByteArrayUnsigned(hash);
				var badrs = 0
				do {
					var k = this.deterministicK(wif, hash, badrs);
					var G = curve.getG();
					var Q = G.multiply(k);
					var r = Q.getX().toBigInteger().mod(n);
					var s = k.modInverse(n).multiply(e.add(priv.multiply(r))).mod(n);
					badrs++
				} while (r.compareTo(BigInteger.ZERO) <= 0 || s.compareTo(BigInteger.ZERO) <= 0);

				// Force lower s values per BIP62
				var halfn = n.shiftRight(1);
				if (s.compareTo(halfn) > 0) {
					s = n.subtract(s);
				};

				var sig = serializeSig(r, s);
				sig.push(parseInt(shType, 10));

				return Crypto.util.bytesToHex(sig);
			} else {
				return false;
			}
		}

		// https://tools.ietf.org/html/rfc6979#section-3.2
		r.deterministicK = function(wif, hash, badrs) {
			// if r or s were invalid when this function was used in signing,
			// we do not want to actually compute r, s here for efficiency, so,
			// we can increment badrs. explained at end of RFC 6979 section 3.2

			// wif is b58check encoded wif privkey.
			// hash is byte array of transaction digest.
			// badrs is used only if the k resulted in bad r or s.

			// some necessary things out of the way for clarity.
			badrs = badrs || 0;
			var key = coinjs.wif2privkey(wif);
			var x = Crypto.util.hexToBytes(key['privkey'])
			var curve = EllipticCurve.getSECCurveByName("secp256k1");
			var N = curve.getN();

			// Step: a
			// hash is a byteArray of the message digest. so h1 == hash in our case

			// Step: b
			var v = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1];

			// Step: c
			var k = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];

			// Step: d
			k = Crypto.HMAC(Crypto.SHA256, v.concat([0]).concat(x).concat(hash), k, { asBytes: true });

			// Step: e
			v = Crypto.HMAC(Crypto.SHA256, v, k, { asBytes: true });

			// Step: f
			k = Crypto.HMAC(Crypto.SHA256, v.concat([1]).concat(x).concat(hash), k, { asBytes: true });

			// Step: g
			v = Crypto.HMAC(Crypto.SHA256, v, k, { asBytes: true });

			// Step: h1
			var T = [];

			// Step: h2 (since we know tlen = qlen, just copy v to T.)
			v = Crypto.HMAC(Crypto.SHA256, v, k, { asBytes: true });
			T = v;

			// Step: h3
			var KBigInt = BigInteger.fromByteArrayUnsigned(T);

			// loop if KBigInt is not in the range of [1, N-1] or if badrs needs incrementing.
			var i = 0
			while (KBigInt.compareTo(N) >= 0 || KBigInt.compareTo(BigInteger.ZERO) <= 0 || i < badrs) {
				k = Crypto.HMAC(Crypto.SHA256, v.concat([0]), k, { asBytes: true });
				v = Crypto.HMAC(Crypto.SHA256, v, k, { asBytes: true });
				v = Crypto.HMAC(Crypto.SHA256, v, k, { asBytes: true });
				T = v;
				KBigInt = BigInteger.fromByteArrayUnsigned(T);
				i++
			};

			return KBigInt;
		};

		/* sign a "standard" input */
		r.signinput = function(index, wif, sigHashType){
			var key = coinjs.wif2pubkey(wif);
			var shType = sigHashType || 1;
			var signature = this.transactionSig(index, wif, shType);
			var s = coinjs.script();
			s.writeBytes(Crypto.util.hexToBytes(signature));
			s.writeBytes(Crypto.util.hexToBytes(key['pubkey']));
			this.ins[index].script = s;
			return true;
		}

		/* signs a time locked / hodl input */
		r.signhodl = function(index, wif, sigHashType){
			var shType = sigHashType || 1;
			var signature = this.transactionSig(index, wif, shType);
			var redeemScript = this.ins[index].script.buffer
			var s = coinjs.script();
			s.writeBytes(Crypto.util.hexToBytes(signature));
			s.writeBytes(redeemScript);
			this.ins[index].script = s;
			return true;
		}
		
		/* sign a multisig input */
		r.signmultisig = function(index, wif, sigHashType){

			function scriptListPubkey(redeemScript){
				var r = {};
				for(var i=1;i<redeemScript.chunks.length-2;i++){
					r[i] = Crypto.util.hexToBytes(coinjs.pubkeydecompress(Crypto.util.bytesToHex(redeemScript.chunks[i])));
				}
				return r;
			}
	
			function scriptListSigs(scriptSig){
				var r = {};
				var c = 0;
				if (scriptSig.chunks[0]==0 && scriptSig.chunks[scriptSig.chunks.length-1][scriptSig.chunks[scriptSig.chunks.length-1].length-1]==174){
					for(var i=1;i<scriptSig.chunks.length-1;i++){				
						if (scriptSig.chunks[i] != 0){
							c++;
							r[c] = scriptSig.chunks[i];
						}
					}
				}
				return r;
			}

			var redeemScript = (this.ins[index].script.chunks[this.ins[index].script.chunks.length-1]==174) ? this.ins[index].script.buffer : this.ins[index].script.chunks[this.ins[index].script.chunks.length-1];

			var pubkeyList = scriptListPubkey(coinjs.script(redeemScript));
			var sigsList = scriptListSigs(this.ins[index].script);

			var shType = sigHashType || 1;
			var sighash = Crypto.util.hexToBytes(this.transactionHash(index, shType));
			var signature = Crypto.util.hexToBytes(this.transactionSig(index, wif, shType));

			sigsList[coinjs.countObject(sigsList)+1] = signature;

			var s = coinjs.script();

			s.writeOp(0);

			for(x in pubkeyList){
				for(y in sigsList){
					this.ins[index].script.buffer = redeemScript;
					sighash = Crypto.util.hexToBytes(this.transactionHash(index, sigsList[y].slice(-1)[0]*1));
					if(coinjs.verifySignature(sighash, sigsList[y], pubkeyList[x])){
						s.writeBytes(sigsList[y]);
					}
				}
			}

			s.writeBytes(redeemScript);
			this.ins[index].script = s;
			return true;
		}

		/* sign segwit input */
		r.signsegwit = function(index, wif, sigHashType){
			var shType = sigHashType || 1;

			var wif2 = coinjs.wif2pubkey(wif);
			var segwit = coinjs.segwitAddress(wif2['pubkey']);
			var bech32 = coinjs.bech32Address(wif2['pubkey']);

			if((segwit['redeemscript'] == Crypto.util.bytesToHex(this.ins[index].script.chunks[0])) || (bech32['redeemscript'] == Crypto.util.bytesToHex(this.ins[index].script.chunks[0]))){
				var txhash = this.transactionHashSegWitV0(index, shType);

				if(txhash.result == 1){

					var segwitHash = Crypto.util.hexToBytes(txhash.hash);
					var signature = this.transactionSig(index, wif, shType, segwitHash);

					// remove any non standard data we store, i.e. input value
					var script = coinjs.script();
					script.writeBytes(this.ins[index].script.chunks[0]);	
					this.ins[index].script = script;

					if(!coinjs.isArray(this.witness)){
						this.witness = [];
					}

					this.witness.push([signature, wif2['pubkey']]);

					/* attempt to reorder witness data as best as we can. 
					   data can't be easily validated at this stage as 
					   we dont have access to the inputs value and 
					   making a web call will be too slow. */

					var witness_order = [];
					var witness_used = [];
					for(var i = 0; i < this.ins.length; i++){
						for(var y = 0; y < this.witness.length; y++){
							if(!witness_used.includes(y)){
								var sw = coinjs.segwitAddress(this.witness[y][1]);
								var b32 = coinjs.bech32Address(this.witness[y][1]);
								var rs = '';

								if(this.ins[i].script.chunks.length>=1){
									rs = Crypto.util.bytesToHex(this.ins[i].script.chunks[0]);
								} else if (this.ins[i].script.chunks.length==0){
									rs = b32['redeemscript'];
								}

								if((sw['redeemscript'] == rs) || (b32['redeemscript'] == rs)){
									witness_order.push(this.witness[y]);
									witness_used.push(y);

									// bech32, empty redeemscript
									if(b32['redeemscript'] == rs){
										this.ins[index].script = coinjs.script();
									}
									break;
								}
							}
						}
					}

					this.witness = witness_order;
				}
			}
			return true;
		}

		/* sign inputs */
		r.sign = function(wif, sigHashType){
			var shType = sigHashType || 1;
			for (var i = 0; i < this.ins.length; i++) {
				var d = this.extractScriptKey(i);

				var w2a = coinjs.wif2address(wif);
				var script = coinjs.script();
				var pubkeyHash = script.pubkeyHash(w2a['address']);

				if(((d['type'] == 'scriptpubkey' && d['script']==Crypto.util.bytesToHex(pubkeyHash.buffer)) || d['type'] == 'empty') && d['signed'] == "false"){
					this.signinput(i, wif, shType);

				} else if (d['type'] == 'hodl' && d['signed'] == "false") {
					this.signhodl(i, wif, shType);

				} else if (d['type'] == 'multisig') {
					this.signmultisig(i, wif, shType);

				} else if (d['type'] == 'segwit') {
					this.signsegwit(i, wif, shType);

				} else {
					// could not sign
				}
			}
			return this.serialize();
		}

		/* serialize a transaction */
		r.serialize = function(){
			var buffer = [];
			buffer = buffer.concat(coinjs.numToBytes(parseInt(this.version),4));

			if(coinjs.isArray(this.witness)){
				buffer = buffer.concat([0x00, 0x01]);
			}

			buffer = buffer.concat(coinjs.numToVarInt(this.ins.length));
			for (var i = 0; i < this.ins.length; i++) {
				var txin = this.ins[i];
				buffer = buffer.concat(Crypto.util.hexToBytes(txin.outpoint.hash).reverse());
				buffer = buffer.concat(coinjs.numToBytes(parseInt(txin.outpoint.index),4));
				var scriptBytes = txin.script.buffer;
				buffer = buffer.concat(coinjs.numToVarInt(scriptBytes.length));
				buffer = buffer.concat(scriptBytes);
				buffer = buffer.concat(coinjs.numToBytes(parseInt(txin.sequence),4));
			}
			buffer = buffer.concat(coinjs.numToVarInt(this.outs.length));

			for (var i = 0; i < this.outs.length; i++) {
				var txout = this.outs[i];
 				buffer = buffer.concat(coinjs.numToBytes(txout.value,8));
				var scriptBytes = txout.script.buffer;
				buffer = buffer.concat(coinjs.numToVarInt(scriptBytes.length));
				buffer = buffer.concat(scriptBytes);
			}

			if((coinjs.isArray(this.witness)) && this.witness.length>=1){
				for(var i = 0; i < this.witness.length; i++){
	 				buffer = buffer.concat(coinjs.numToVarInt(this.witness[i].length));
					for(var x = 0; x < this.witness[i].length; x++){
		 				buffer = buffer.concat(coinjs.numToVarInt(Crypto.util.hexToBytes(this.witness[i][x]).length));
						buffer = buffer.concat(Crypto.util.hexToBytes(this.witness[i][x]));
					}
				}
			}

			buffer = buffer.concat(coinjs.numToBytes(parseInt(this.lock_time),4));
			return Crypto.util.bytesToHex(buffer);
		}

		/* deserialize a transaction */
		r.deserialize = function(buffer){
			if (typeof buffer == "string") {
				buffer = Crypto.util.hexToBytes(buffer)
			}

			var pos = 0;
			var witness = false;

			var readAsInt = function(bytes) {
				if (bytes == 0) return 0;
				pos++;
				return buffer[pos-1] + readAsInt(bytes-1) * 256;
			}

			var readVarInt = function() {
				pos++;
				if (buffer[pos-1] < 253) {
					return buffer[pos-1];
				}
				return readAsInt(buffer[pos-1] - 251);
			}

			var readBytes = function(bytes) {
				pos += bytes;
				return buffer.slice(pos - bytes, pos);
			}

			var readVarString = function() {
				var size = readVarInt();
				return readBytes(size);
			}

			var obj = new coinjs.transaction();
			obj.version = readAsInt(4);

			if(buffer[pos] == 0x00 && buffer[pos+1] == 0x01){
				// segwit transaction
				witness = true;
				obj.witness = [];
				pos += 2;
			}

			var ins = readVarInt();
			for (var i = 0; i < ins; i++) {
				obj.ins.push({
					outpoint: {
						hash: Crypto.util.bytesToHex(readBytes(32).reverse()),
 						index: readAsInt(4)
					},
					script: coinjs.script(readVarString()),
					sequence: readAsInt(4)
				});
			}

			var outs = readVarInt();
			for (var i = 0; i < outs; i++) {
				obj.outs.push({
					value: coinjs.bytesToNum(readBytes(8)),
					script: coinjs.script(readVarString())
				});
			}

			if(witness == true){
				for (i = 0; i < ins; ++i) {
					var count = readVarInt();
					var vector = [];
					for(var y = 0; y < count; y++){
						var slice = readVarInt();
						pos += slice;
						if(!coinjs.isArray(obj.witness[i])){
							obj.witness[i] = [];
						}
						obj.witness[i].push(Crypto.util.bytesToHex(buffer.slice(pos - slice, pos)));
					}
				}
			}

 			obj.lock_time = readAsInt(4);
			return obj;
		}

		r.size = function(){
			return ((this.serialize()).length/2).toFixed(0);
		}

		return r;
	}

	/* start of signature vertification functions */

	coinjs.verifySignature = function (hash, sig, pubkey) {

		function parseSig (sig) {
			var cursor;
			if (sig[0] != 0x30)
				throw new Error("Signature not a valid DERSequence");

			cursor = 2;
			if (sig[cursor] != 0x02)
				throw new Error("First element in signature must be a DERInteger"); ;

			var rBa = sig.slice(cursor + 2, cursor + 2 + sig[cursor + 1]);

			cursor += 2 + sig[cursor + 1];
			if (sig[cursor] != 0x02)
				throw new Error("Second element in signature must be a DERInteger");

			var sBa = sig.slice(cursor + 2, cursor + 2 + sig[cursor + 1]);

			cursor += 2 + sig[cursor + 1];

			var r = BigInteger.fromByteArrayUnsigned(rBa);
			var s = BigInteger.fromByteArrayUnsigned(sBa);

			return { r: r, s: s };
		}

		var r, s;

		if (coinjs.isArray(sig)) {
			var obj = parseSig(sig);
			r = obj.r;
			s = obj.s;
		} else if ("object" === typeof sig && sig.r && sig.s) {
			r = sig.r;
			s = sig.s;
		} else {
			throw "Invalid value for signature";
		}

		var Q;
		if (coinjs.isArray(pubkey)) {
			var ecparams = EllipticCurve.getSECCurveByName("secp256k1");
			Q = EllipticCurve.PointFp.decodeFrom(ecparams.getCurve(), pubkey);
		} else {
			throw "Invalid format for pubkey value, must be byte array";
		}
		var e = BigInteger.fromByteArrayUnsigned(hash);

		return coinjs.verifySignatureRaw(e, r, s, Q);
	}

	coinjs.verifySignatureRaw = function (e, r, s, Q) {
		var ecparams = EllipticCurve.getSECCurveByName("secp256k1");
		var n = ecparams.getN();
		var G = ecparams.getG();

		if (r.compareTo(BigInteger.ONE) < 0 || r.compareTo(n) >= 0)
			return false;

		if (s.compareTo(BigInteger.ONE) < 0 || s.compareTo(n) >= 0)
			return false;

		var c = s.modInverse(n);

		var u1 = e.multiply(c).mod(n);
		var u2 = r.multiply(c).mod(n);

		var point = G.multiply(u1).add(Q.multiply(u2));

		var v = point.getX().toBigInteger().mod(n);

		return v.equals(r);
	}

	/* start of privates functions */

	/* base58 encode function */
	coinjs.base58encode = function(buffer) {
		var alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
		var base = BigInteger.valueOf(58);

		var bi = BigInteger.fromByteArrayUnsigned(buffer);
		var chars = [];

		while (bi.compareTo(base) >= 0) {
			var mod = bi.mod(base);
			chars.unshift(alphabet[mod.intValue()]);
			bi = bi.subtract(mod).divide(base);
		}

		chars.unshift(alphabet[bi.intValue()]);
		for (var i = 0; i < buffer.length; i++) {
			if (buffer[i] == 0x00) {
				chars.unshift(alphabet[0]);
			} else break;
		}
		return chars.join('');
	}

	/* base58 decode function */
	coinjs.base58decode = function(buffer){
		var alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
		var base = BigInteger.valueOf(58);
		var validRegex = /^[1-9A-HJ-NP-Za-km-z]+$/;

		var bi = BigInteger.valueOf(0);
		var leadingZerosNum = 0;
		for (var i = buffer.length - 1; i >= 0; i--) {
			var alphaIndex = alphabet.indexOf(buffer[i]);
			if (alphaIndex < 0) {
				throw "Invalid character";
			}
			bi = bi.add(BigInteger.valueOf(alphaIndex).multiply(base.pow(buffer.length - 1 - i)));

			if (buffer[i] == "1") leadingZerosNum++;
			else leadingZerosNum = 0;
		}

		var bytes = bi.toByteArrayUnsigned();
		while (leadingZerosNum-- > 0) bytes.unshift(0);
		return bytes;		
	}

	/* raw ajax function to avoid needing bigger frame works like jquery, mootools etc */
	coinjs.ajax = function(u, f, m, a){
		var x = false;
		try{
			x = new ActiveXObject('Msxml2.XMLHTTP')
		} catch(e) {
			try {
				x = new ActiveXObject('Microsoft.XMLHTTP')
			} catch(e) {
				x = new XMLHttpRequest()
			}
		}

		if(x==false) {
			return false;
		}

		x.open(m, u, true);
		x.onreadystatechange=function(){
			if((x.readyState==4) && f)
				f(x.responseText);
		};

		if(m == 'POST'){
			x.setRequestHeader('Content-type','application/x-www-form-urlencoded');
		}

		x.send(a);
	}

	/* clone an object */
	coinjs.clone = function(obj) {
		if(obj == null || typeof(obj) != 'object') return obj;
		var temp = new obj.constructor();

		for(var key in obj) {
			if(obj.hasOwnProperty(key)) {
				temp[key] = coinjs.clone(obj[key]);
			}
		}
 		return temp;
	}

	coinjs.numToBytes = function(num,bytes) {
		if (typeof bytes === "undefined") bytes = 8;
		if (bytes == 0) { 
			return [];
		} else if (num == -1){
			return Crypto.util.hexToBytes("ffffffffffffffff");
		} else {
			return [num % 256].concat(coinjs.numToBytes(Math.floor(num / 256),bytes-1));
		}
	}

	function scriptNumSize(i) {
		return i > 0x7fffffff ? 5
			: i > 0x7fffff ? 4
			: i > 0x7fff ? 3
			: i > 0x7f ? 2
			: i > 0x00 ? 1
			: 0;
	}

	coinjs.numToScriptNumBytes = function(_number) {
		var value = Math.abs(_number);
		var size = scriptNumSize(value);
		var result = [];
		for (var i = 0; i < size; ++i) {
			result.push(0);
		}
		var negative = _number < 0;
		for (i = 0; i < size; ++i) {
			result[i] = value & 0xff;
			value = Math.floor(value / 256);
		}
		if (negative) {
			result[size - 1] |= 0x80;
		}
		return result;
	}

	coinjs.numToVarInt = function(num) {
		if (num < 253) {
			return [num];
		} else if (num < 65536) {
			return [253].concat(coinjs.numToBytes(num,2));
		} else if (num < 4294967296) {
			return [254].concat(coinjs.numToBytes(num,4));
		} else {
			return [255].concat(coinjs.numToBytes(num,8));
		}
	}

	coinjs.bytesToNum = function(bytes) {
		if (bytes.length == 0) return 0;
		else return bytes[0] + 256 * coinjs.bytesToNum(bytes.slice(1));
	}

	coinjs.uint = function(f, size) {
		if (f.length < size)
			throw new Error("not enough data");
		var n = 0;
		for (var i = 0; i < size; i++) {
			n *= 256;
			n += f[i];
		}
		return n;
	}

	coinjs.isArray = function(o){
		return Object.prototype.toString.call(o) === '[object Array]';
	}

	coinjs.countObject = function(obj){
		var count = 0;
		var i;
		for (i in obj) {
			if (obj.hasOwnProperty(i)) {
				count++;
			}
		}
		return count;
	}

	coinjs.random = function(length) {
		var r = "";
		var l = length || 25;
		var chars = "!$%^&*()_+{}:@~?><|\./;'#][=-abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890";
		for(x=0;x<l;x++) {
			r += chars.charAt(Math.floor(Math.random() * 62));
		}
		return r;
	}

})();
 //next 

