(function () {
	var nojro = window.nojro = function () { };
	nojro.node	= ((document.location.hostname.split(".")[(document.location.hostname.split(".")).length-1]) == 'noj') ? 'accesscoin.noj' : 'accesscoinx.com';
	nojro.rpc = ('https:'==document.location.protocol?'https://':'http://')+nojro.hostname+'/api/';

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
		return a;
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
})();