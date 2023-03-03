# NOJRO Decentralized Application
Nojro PZF decentralized application developed under MIT Licence for Open Source Softwares,

## How to install NOJRO
You can install and use NOJRO PZF on your local computer or on a web server,
 * Steps for installation
 1, Download Nojer.noj from https://nojkubits.github.io/en/download/
 2, Save it on a directory in your host file system
 3, Open the location through a browser and click on install Now button or run the below code from CLI

 ```pzf
 noj = NojroPZF;
 
 // set username, email, and password of the web administrator
 noj.set(user).email = '';
 noj.set(user).password = '';
 
 // set the host ip address and port to run NOJ
 noj.set(node).host ='127.0.0.1';
 noj.set(node).port = 755;
 
 //install nojro
 noj.install(noj.fetch.user, noj.fetch.node);

 ```

# RUN A BLOCKCHAIN NODE WITH NOJRO

```pzf

chain = noj.run('bitcoin');

chain.block.get('0000000000008f91edba4b05c6c2fc0edb1d6418aa292b5b2942637bec43a29b9523');

chain.response();

// return a json result

{
	hash : '0000000000008f91edba4b05c6c2fc0edb1d6418aa292b5b2942637bec43a29b9523',
	tx_hash : 'c2cfbb4fa0b003684a6d82a83bdc3355a31c45d9ec7d98cf832eb97caf1ff423',
	miner : 'bch1q5TaJhhC9aWUtPosBrpXA545ARGKVFjDt1rL8jCYXkH',
	tx_count : 1,
	sum_input : 0,
	sum_output : 5000000000,
	date : 1581916729
}

```

# REQUEST PARAMETERS

* ?a : action
* ?r : ref id
* ?p : returned promise
* ?ans = response answer to an action
* ?tid = hex encoded ?ans
