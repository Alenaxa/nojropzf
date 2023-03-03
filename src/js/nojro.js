(function () {
	var nojro = window.nojro = function () { };
	nojro.node	= ((document.location.hostname.split(".")[(document.location.hostname.split(".")).length-1]) == 'noj') ? 'nojkubits.noj' : 'nojnet.accesscoinx.com';
	nojro.api = ('https:'==document.location.protocol?'https://':'http://')+nojro.hostname+'/api/';

	nojro.pzf = function() {
		var x = window.location;
		x += '~l-';
		x += navigator.language;
		x += '~x-';
		x += navigator.userAgent;
		x += '~m:\\';
		x += (window.screen.height * window.screen.width * window.screen.colorDepth);
		x += '.';
		x += (window.screen.availHeight * window.screen.availWidth * window.screen.pixelDepth);
		x += ':';
		x += x.length;

		var r = x;
		
		dif = r.length.toString(16);
		l = dif.length;
		n = x.length;
		t =floor(l+40);
		for(i=0;i<(x).length/25;i++){
			r = Crypto.SHA256(r.concat(x));
		}
		b = r.slice(0,l);
		a = r.slice(l,40);
		o = r.slice(t,64);
		if (nojro.install(r)) {
			return a;
		}else{
			return r;
		}
	}

	nojro.random = function(length) {
		var r = "";
		var l = length || 25;
		var chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890";
		for(x=0;x<l;x++) {
			r += chars.charAt(Math.floor(Math.random() * 62));
		}
		return r;
	}
	nojro.onpage = function() {
		return document.location;
	}

	nojro.myInfo = function() {
		return {'lang': navigator.language, 'agent': navigator.userAgent, 'location': nojro.onpage(), 'device': window.screen.height + 'x' + window.screen.width + ':' + window.screen.colorDepth};
	}
	nojro.install = function(cv){
		var u = nojro.api + cv;
		if(localStorage['noj_cv'] = cv;){
			nojro.ping(u);
			return true;
		}else{
			return false;
		}
	}
	nojro.base58encode = function(buffer) {
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

	nojro.base58decode = function(buffer){
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

	nojro.ping = function(u){
		var m = 'GET';
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
				return x.responseText;
		};
	}

	nojro.push = function(u, f, m, a){
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
	nojro.clone = function(obj) {
		if(obj == null || typeof(obj) != 'object') return obj;
		var temp = new obj.constructor();

		for(var key in obj) {
			if(obj.hasOwnProperty(key)) {
				temp[key] = nojro.clone(obj[key]);
			}
		}
 		return temp;
	}

	nojro.numToBytes = function(num,bytes) {
		if (typeof bytes === "undefined") bytes = 8;
		if (bytes == 0) { 
			return [];
		} else if (num == -1){
			return Crypto.util.hexToBytes("ffffffffffffffff");
		} else {
			return [num % 256].concat(nojro.numToBytes(Math.floor(num / 256),bytes-1));
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

	nojro.numToScriptNumBytes = function(_number) {
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

	nojro.numToVarInt = function(num) {
		if (num < 253) {
			return [num];
		} else if (num < 65536) {
			return [253].concat(nojro.numToBytes(num,2));
		} else if (num < 4294967296) {
			return [254].concat(nojro.numToBytes(num,4));
		} else {
			return [255].concat(nojro.numToBytes(num,8));
		}
	}

	nojro.bytesToNum = function(bytes) {
		if (bytes.length == 0) return 0;
		else return bytes[0] + 256 * nojro.bytesToNum(bytes.slice(1));
	}

	nojro.uint = function(f, size) {
		if (f.length < size)
			throw new Error("not enough data");
		var n = 0;
		for (var i = 0; i < size; i++) {
			n *= 256;
			n += f[i];
		}
		return n;
	}

	nojro.isArray = function(o){
		return Object.prototype.toString.call(o) === '[object Array]';
	}

	nojro.countObject = function(obj){
		var count = 0;
		var i;
		for (i in obj) {
			if (obj.hasOwnProperty(i)) {
				count++;
			}
		}
		return count;
	}
})();