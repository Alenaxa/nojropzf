# NOJRO Decentralized Application
Nojro PZF decentralized application developed under MIT Licence for Open Source Softwares,

## How to install NOJRO
You can install and use NOJRO PZF on your local computer or on a web server,
 - via web source
 - Download Nojer.pzf from https://nojropzf.github.io/download
 - Extract to a directory in your localhost
 - Open the dir via browser, So simple.
 
 - via Console

 ```git
 git clone https://github.com/alenaxa/nojropzf
 ```

# RUNNING A DLT NETWORK NODE

```pzf
var nojro = PZF();
nojro->network(0,'bitcoin');
nojro->network->cli("latestBlock");
```
// return a json result
```json
{
	block: '0000000000008f91edba4b05c6c2fc0edb1d6418aa292b5b2942637bec43a29b9523',
	height: 170,
	tx_hash: 'c2cfbb4fa0b003684a6d82a83bdc3355a31c45d9ec7d98cf832eb97caf1ff423',
	sum_output : 5000000000,
	mediantime : 1581916729,
	....
}
```
