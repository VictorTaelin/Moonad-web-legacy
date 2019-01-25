keccak256 = require("./keccak");
udp = require('dgram');

// useful constants
const empty_hash = "0000000000000000000000000000000000000000000000000000000000000000"

// Useful functions
function hash(strings) {
    return keccak256(strings.join(""));
};

function randomInt(max){
    return Math.trunc(Math.random() * max);
}

function median(numbers) {
    var median = 0;
    var nums = numbers.slice(); // Copy input array to avoid mutability
    var numsLen = nums.length;
    nums.sort();

    if (nums > 0) {
        if (nums % 2 === 0) {
            // average of two middle numbers
            median = (nums[numsLen / 2 - 1] + nums[numsLen / 2]) / 2;
        }
        else {
            // middle number only
            median = nums[(numsLen - 1) / 2];
        }
    }
    return median;
}

function empty_block(extra, prev_hash) {
    return new Block(
        "0000000000000000",
        "0000000000000000",
        extra || "00000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        prev_hash || "0000000000000000000000000000000000000000000000000000000000000000",
        hash([]),
        []);
}

class Block {
    constructor(time, nonce, extra, difficulty, prev_hash, posts_hash, posts = []) {
        this.time = time // string (hex of 64 bits, POSIX time)
        this.nonce = nonce // string (hex of 64 bits)
        this.extra = extra // string (hex of 128 bits)
        this.difficulty = difficulty // string (hex of 256 bits)
        this.prev_hash = prev_hash // string (hex of 256 bits)
        this.posts_hash = posts_hash // string (hex of 256 bits)
        this.posts = posts // [string]
    };

    hash() {
        return hash([this.time, this.nonce, this.extra, this.difficulty, this.prev_hash, this.posts_hash])
    };

    set_posts(posts){
        this.posts = posts
    };

    is_valid() {
        return this.posts_hash == hash(this.posts)
    };

    show() {
        var text = ""
        text  = "- time       = " + this.time + "\n"
        text += "- nonce      = " + this.nonce + "\n"
        text += "- extra      = " + this.extra + "\n"
        text += "- difficulty = " + this.difficulty + "\n"
        text += "- prev_hash  = " + this.prev_hash + "\n"
        text += "- posts_hash = " + this.posts_hash + "\n"
        text += "- posts:\n"
        for (var i = 0; i < this.posts.lenght; i++ ) {
            text += "-- " + posts[i]
        }
        return text
    };

    to_json() {
        var json = {
            'hash':this.hash(),
            'time':this.time,
            'nonce':this.nonce,
            'extra':this.extra,
            'difficulty':this.difficulty,
            'prev_hash':this.prev_hash,
            'posts_hash':this.posts_hash,
            'posts':this.posts
        };
        return json;
    };

    from_json(json) {
        this.time = json.time // string (hex of 64 bits, POSIX time)
        this.nonce = json.nonce // string (hex of 64 bits)
        this.extra = json.extra // string (hex of 128 bits)
        this.difficulty = json.difficulty // string (hex of 256 bits)
        this.prev_hash = json.prev_hash // string (hex of 256 bits)
        this.posts_hash = json.posts_hash // string (hex of 256 bits)
        this.posts = json.posts // [string]
        return this;
    }
}

class Blockchain {
    constructor(){
        this.blocks = {};
    };

    add(block) {
        if (!block.is_valid()) {
            throw "Attempted to add invalid block."
        }
        this.blocks[block.hash()] = block;
    };

    block_height(block_hash) {
        if (block_hash == empty_hash) {
            return 0;
        } else if (!this.blocks[block_hash]) {
            return null;
        } else {
            var prev_height = this.block_height(this.blocks[block_hash].prev_hash);
            if (prev_height !== null) {
                return prev_height + 1;
            } else {
                return null;
            }
        }
    };

    // Get the block with the highest heigh
    get_tip() {
        var tip = empty_hash;

        for (var block_hash in this.blocks) {
            if (this.block_height(block_hash) > this.block_height(tip)) {
                tip = block_hash;
            }
        }

        return tip;
    };

    show() {
        var text = '';

        for (var block_hash in this.blocks) {
            text += 'Block hash   : ' + block_hash + '\n';
            text += '- height     = ' + this.block_height(block_hash) + '\n';
            text += this.blocks[block_hash].show() + '\n';
        };
        return text;
    };
}

class Peer {
    constructor(host, port, offset){
        this.host = host;
        this.port = port;
        this.offset = offset; // difference between local and remote UTC times.
    };
}

class Client {
    constructor(host, port, remoteHost, remotePort) {
        this.host = host; // Client address in the network
        this.port = port; // Port to which the client will listen
        this.remoteHost = remoteHost; // First node to which attempt a connection
        this.remotePort = remotePort;
        this.peers = []; // Peers to which the client is connected.
        this.blockchain = new Blockchain; // TODO: Save blockchain in a file
        this.socket = udp.createSocket('udp4');
    };

    // Returns a random peer from Client.peers
    randomPeer(){
        return this.peers[randomInt(this.peers.length)];
    };

    // returns current elapsed time from Epoch (01 January 1970) in seconds
    localTime() {
        return Math.round(Date.now()/1000);
    };

    // Whenever a node connects to another node, it gets a UTC timestamp from it,
    // and stores its offset from node-local UTC. The network-adjusted time is then
    // the node-local UTC plus the median offset from all connected nodes.
    // Network time is never adjusted more than 70 minutes from local system
    // time, however.
    networkAdjustedTime() {
        var offsets = [];
        this.peers.forEach(function(peer, index) {
            offsets.push(peer.offset);
        });

        var medianOffset = median(offsets);
        if (medianOffset > 4200) {
            medianOffset = 4200;
        }
        else if (medianOffset < -4200) {
            medianOffset = -4200;
        }
        return this.localTime() + medianOffset;
    };

    // Returns TRUE if peer is not connected and FALSE otherwise
    peerIsNew(peer) {
        var isNew = true;
        // If 'peer' has the same address as 'client' return FALSE
        if ((peer.host == this.host) && (peer.port == this.port)) {
            isNew = false;
        }
        // Else, look for peer in the list of connected peers
        this.peers.forEach(function (knownPeer, index) {
            if((knownPeer.host == peer.host) && (knownPeer.port == peer.port)) {
                isNew = false;
            }
        });
        return isNew;
    };

    // Adds a new peer to this.peers where
    // remoteHost - the address of the remote node
    // remotePort - the port to which the remote node is listening
    // remoteTime - the UTC timestamp received from the remote node
    addPeer(remoteHost, remotePort, remoteTime) {
        var peer = new Peer(remoteHost, remotePort, 0);
        console.log("ADD_PEER: " + JSON.stringify(peer));
        if (this.peerIsNew(peer)) {
            var offset = this.localTime() - remoteTime;
            peer.offset = offset;
            this.peers.push(peer);

            /////// DEBUGGING ONLY! ///////
            //TODO: Delete this piece of code for release
            console.log("Connection accepted. Time Offset = " + offset +
            "\tNAT = " + this.networkAdjustedTime());
            console.log(this.peers);
            /////// DEBUGGING ONLY! ///////

            return peer;
        }
        return
    };

    sendMsg(msg, peer) {
        this.socket.send(msg, peer.port, peer.host, function(error){
            if(error){
                console.log("Error: " + error);
            }
        });
    };

    requestConnection(peer){
        var msg = requestConnJson;
        msg.host = this.host;
        msg.port = this.port
        msg.time = this.localTime();
        this.sendMsg(JSON.stringify(msg), peer);
    };

    getPeers(peer) {
        var msg = getPeersJson;
        msg.host = this.host;
        msg.port = this.port;
        this.sendMsg(JSON.stringify(msg), peer);
    };

    getTip(peer) {
        var msg = getTipJson;
        msg.host = this.host;
        msg.port = this.port;
        this.sendMsg(JSON.stringify(msg), peer);
    };

    getBlock(hash, peer) {
        var msg = getBlkJson;
        msg.host = this.host;
        msg.port = this.port;
        msg.hash = hash;
        this.sendMsg(JSON.stringify(msg), peer);
    };

    broadcast(msg) {
        this.peers.forEach(function(peer, index) {
            this.sendMsg(msg, peer);
        }.bind(this));
    };

    broadcastBlock(blk){
        var msg = sendBlockJson;
        msg.host = this.host;
        msg.port = this.port;
        msg.hash = blk.hash();
        msg.block = blk;
        this.broadcast(JSON.stringify(msg));
    };

    timestampIsValid(block){
        /*A timestamp is accepted as valid if it is greater than the median
        timestamp of previous 11 blocks, and less than the network-adjusted
        time + 2 hours. "Network-adjusted time" is the median of the timestamps
        returned by all nodes connected to you. */

        // ATTENTION!
        // Currently, the function accepts all timestamps if the Blockchain
        // has length < 11.
        // TODO: Look for a better solution

        var itt = 0;
        var prevHash = block.prev_hash;
        var prevBlk;
        do {
            prevBlk = blockchain.blocks[prevHash];
            prevHash = prevBlk.prev_hash;
            itt++;
        } while ((itt < 6) && prevBlk !== undefined);

        if (prevBlk !== undefined) {
            var medianTimestamp = prevBlk.time;
            return (((block.time > medianTimestamp) &&
                     (block.time < this.networkAdjustedTime() + 7200)) ||
                     (Object.keys(this.blockchain.blocks).length < 11)); // If blockchain len < 11, return TRUE
        }
        return false;
    };

    init() {
        this.blockchain.add(empty_block()); // include a genesis block
        this.socket.bind(this.port);
        /* Socket Event Handlers */
        // emits on new datagram msg
        this.socket.on('message',function(msg, remote) {
            //console.log(msg.toString() + ' <<<<< ' + remote.port);
            var req = JSON.parse(msg);

            switch(req.type){
                //---------------------------------------------------------------------
                case requestConnJson.type:
                // Another client requested a connection
                    console.log("Received connection request from " + req.port + " with time = " + req.time);
                    this.addPeer(req.host, req.port, req.time);
                    var respPeer = new Peer(req.host, req.port, 0);
                    var resp = acceptConnJson;
                    resp.host = this.host;
                    resp.port = this.port;
                    resp.time = this.localTime();
                    console.log("Sending response: " + JSON.stringify(resp));
                    this.sendMsg(JSON.stringify(resp), respPeer);
                break;

                //---------------------------------------------------------------------
                case acceptConnJson.type:
                // Another client accepted my connection request
                console.log("Connection accepted from " + req.port + " with time = " + req.time);
                this.addPeer(req.host, req.port, req.time);
                break;

                //---------------------------------------------------------------------
                case getPeersJson.type:
                // Another client requested list of peers
                var db = sendPeersJson
                db.peers = this.peers.slice();
                var respPeer = new Peer(req.host, req.port, 0);
                this.sendMsg(JSON.stringify(db), respPeer);
                break;

                //---------------------------------------------------------------------
                // Another client requested a specific block
                case getBlkJson.type:
                var msg = sendBlockJson;
                msg.block = this.blockchain.blocks[req.hash];
                msg.hash = req.hash;
                var respPeer = new Peer(req.host, req.port, 0);
                this.sendMsg(JSON.stringify(msg), respPeer);
                break;

                //---------------------------------------------------------------------
                // Another client requested blockchain tip
                case getTipJson.type:
                var msg = sendBlockJson;
                msg.block = this.blockchain.blocks[this.blockchain.get_tip()];
                msg.hash = this.blockchain.get_tip();
                var respPeer = new Peer(req.host, req.port, 0);
                this.sendMsg(JSON.stringify(msg), respPeer);
                break;

                //---------------------------------------------------------------------
                // Received response from getPeers
                case sendPeersJson.type:
                req.peers.forEach(function(peer, index) {
                    // TODO: Implement a way to resend request in case a response does
                    // not arrive
                    if (this.peerIsNew(peer)) {
                        this.requestConnection(peer);
                    }
                }.bind(this));
                break;

                //---------------------------------------------------------------------
                // Received block
                case sendBlockJson.type:
                if (req.block) {
                    var newBlock = new Block;
                    newBlock.from_json(req.block);
                    // check if block is valid and not yet on local blockchain copy
                    if ((newBlock.is_valid()) &&
                        (newBlock.hash() === req.hash) &&
                        (!this.blockchain.blocks[req.hash])) {
                        // add block to blockchain
                        this.blockchain.add(newBlock);
                        // broadcast block to other peers
                        this.broadcastBlock(newBlock);
                        console.log("Blockchain len = " + Object.keys(this.blockchain.blocks).length);
                        // if previous block is not on local blockchain copy, request previous block
                        if(!this.blockchain.blocks[req.block.prev_hash]){
                            var respPeer = new Peer(req.host, req.port, 0);
                            this.getBlock(req.block.prev_hash, respPeer);
                        }
                    }
                }
                break;

                //---------------------------------------------------------------------
                default:
                console.log("Received invalid message. Ignoring...");
                break;
            }

        }.bind(this));

        // emits when socket is ready and listening for datagram msgs
        this.socket.on('listening',function(){
            var address = this.socket.address();
            var port = address.port;
            var family = address.family;
            var ipaddr = address.address;
            console.log('Listening at port ' + port);
            console.log('IP :' + ipaddr);
            console.log('IP4/IP6 : ' + family);
        }.bind(this));

        // emits when any error occurs
        this.socket.on('error', function(error){
            console.log("Error: " + error);
            socket.close();
        }.bind(this));

        //emits after the socket is closed using socket.close();
        this.socket.on('close',function(){
            console.log('Socket is closed !');
        }.bind(this));
    };

    run() {
        //------------- TESTS -------------\\
        // getPeers
        // ATTENTION!
        // If the local node receives a connection request, it will stop trying
        // to connect to the original 'remote' node. If this happens, it is possible
        // that the local node accidentally isolates itself from the main chain.
        // TODO: Solve this issue by forcing the node to connect to its origial
        // 'remote' node even after accepting connections from different nodes.
        setInterval(function() {
            //console.log("getPeers");
            if (this.peers.length > 0){
                var remote = this.randomPeer();
                this.getPeers(remote);
            }
            else {
                var remote = new Peer(this.remoteHost, this.remotePort, 0);
                this.requestConnection(remote);
            }
        }.bind(this),5000);

        // getTip
        setInterval(function() {
            //console.log("getTip");
            if (this.peers.length > 0){
                var remote = this.randomPeer();
                this.getTip(remote);
            }
        }.bind(this),6000);

        // newBlock
        setInterval(function(){
            console.log("Discovered new block!");
            // create block
            var blk = new Block(
                this.localTime(),
                "0000000000000000",
                "00000000000000000000000000000000",
                "0000000000000000000000000000000000000000000000000000000000000000",
                this.blockchain.get_tip(),
                hash([]),
                []);
            // add block to Blockchain
            this.blockchain.add(blk);
            console.log("===> Blockchain len = " + Object.keys(this.blockchain.blocks).length);
            // Broadcast new block
            this.broadcastBlock(blk);
        }.bind(this), 10000);
    };
}

// 'Client' class private constants
const requestConnJson = {'type':'requestConn', 'host':'localhost', 'port':-1, 'time':0};
const acceptConnJson = {'type':'acceptConn', 'host':'localhost', 'port':-1, 'time':0};
const getPeersJson = {'type':'getPeers', 'host':'localhost', 'port':-1};
const getBlkJson = {'type':'getBlk', 'host':'localhost', 'port':-1, 'hash':empty_hash};
const getTipJson = {'type':'getTip', 'host':'localhost', 'port':-1};
const sendBlockJson = {'type':'block', 'host':'localhost', 'port':-1, 'hash':empty_hash, 'block':{}};
const sendPeersJson = {'type':'addr', 'peers':[]};


function main() {
    var blockchain = new Blockchain();

    var block_0 = empty_block();
    blockchain.add(block_0);

    var block_1 = empty_block(block_0.hash());
    blockchain.add(block_1);

    var block_2 = empty_block(block_1.hash());
    blockchain.add(block_2);

    var block_3 = empty_block(block_2.hash());
    blockchain.add(block_3);

    var block_4 = empty_block("without previous block");
    blockchain.add(block_4);

    console.log(blockchain.show());
    console.log("> Tip");
    console.log(blockchain.get_tip());
}

module.exports = {
    Block: Block,
    Blockchain: Blockchain,
    Peer: Peer,
    Client: Client,
    hash: hash,
    empty_hash: empty_hash,
}


// test();
//main();
