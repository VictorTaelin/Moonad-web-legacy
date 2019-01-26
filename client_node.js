const udp = require('dgram');
const eth = require('./ethernal');

if (process.argv.length != 4) {
    console.log("Usage: \"node client_node [LOCAL_PORT] [REMOTE_PORT]\"\n");
    console.log("Where LOCAL_PORT is the port used by client_node to communicate");
    console.log("with other clients and REMOTE_PORT is the port used by another");
    console.log("instance of client_node\n");
    console.log("e.g.: node client_node 5000 5001");
    process.exit();
}

// Useful constants
const PORT = parseInt(process.argv[2]);
const REMOTE = parseInt(process.argv[3]);

// useful variables
var blockchain = new eth.Blockchain; // TODO: Save blockchain in a file
blockchain.add(empty_block()); //TODO: testing only. Remove this line on release
var socket = udp.createSocket('udp4');
socket.bind(PORT);
var timeOffset = [];

// Peer Database
var db = {'type':'addr', 'peers':[]};

// Message Templates
const requestConnJson = {'type':'requestConn', 'port':PORT, 'time':0};
const acceptConnJson = {'type':'acceptConn', 'port':PORT, 'time':0};
const getPeersJson = {'type':'getPeers', 'port':PORT};
const getBlkJson = {'type':'getBlk', 'port':PORT, 'hash':eth.empty_hash};
const getTipJson = {'type':'getTip', 'port':PORT};
const sendBlockJson = {'type':'block', 'port':PORT, 'hash':eth.empty_hash, 'block':empty_block()};

/* Useful general functions */
function randomInt(max){
    return Math.trunc(Math.random() * max);
}

function randomPeer(){
    return db.peers[randomInt(db.peers.length)];
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

// returns current elapsed time from Epoch (01 January 1970) in seconds
function localTime() {
    return Math.round(Date.now()/1000);
}

function networkAdjustedTime() {
    /* Whenever a node connects to another node, it gets a UTC timestamp from it,
    and stores its offset from node-local UTC. The network-adjusted time is then
    the node-local UTC plus the median offset from all connected nodes.
    Network time is never adjusted more than 70 minutes from local system
    time, however.*/
    var offset = median(timeOffset);
    if (offset > 4200) {
        offset = 4200;
    }
    else if (offset < -4200) {
        offset = -4200;
    }
    return localTime() + offset;
}

/* Useful network functions */
function peerIsNew(peer) {
    return ((!db.peers.includes(peer)) && (peer != PORT));
}

function pushNewPeer(peer, peerTime) {
    if (peerIsNew(peer)) {
        var offset = localTime() - peerTime;
        timeOffset.push(offset);
        db.peers.push(peer);
        console.log("Connection accepted. Time Offset = " + offset +
        "\tNAT = " + networkAdjustedTime());
        console.log(db);
    }
}

function sendMsg(msg, port) {
    socket.send(msg, port,'localhost', function(error){
        if(error){
            console.log("Error: " + error);
        }else{
            //console.log(msg + ' >>>>> ' + port);
        }
    });
}

function requestConnection(peer){
    var msg = requestConnJson;
    msg.time = localTime();
    sendMsg(JSON.stringify(msg), peer);
}

function getPeers(remote) {
    sendMsg(JSON.stringify(getPeersJson), remote);
}

function getTip(remote) {
    sendMsg(JSON.stringify(getTipJson), remote);
}

function getBlock(hash, remote) {
    var getBlk = getBlkJson;
    getBlk.hash = hash;
    sendMsg(JSON.stringify(getBlk), remote);
}

function broadcast(msg) {
    db.peers.forEach(function(peer, index) {
        sendMsg(msg, peer);
    });
}

function broadcastBlock(blk){
    var msg = sendBlockJson;
    msg.hash = blk.hash();
    msg.block = blk;
    broadcast(JSON.stringify(msg));
}

function timestampIsValid(block){
    /*A timestamp is accepted as valid if it is greater than the median
    timestamp of previous 11 blocks, and less than the network-adjusted
    time + 2 hours. "Network-adjusted time" is the median of the timestamps
    returned by all nodes connected to you. */
    var itt = 0;
    var prevHash = block.prev_hash;
    var prevBlk;
    do {
        prevBlk = blockchain.blocks[prevHash];
        prevHash = prevBlk.prev_hash;
        itt++;
    } while ((itt < 6) && prevHash != undefined);

    var medianTimestamp = prevBlk.time;
    return (((block.time > medianTimestamp) &&
             (block.time < networkAdjustedTime + 7200)) ||
             (Object.keys(blockchain.blocks).length < 11));
}

/* Socket Event Handlers */
// emits on new datagram msg
socket.on('message',function(msg, remote){
    //console.log(msg.toString() + ' <<<<< ' + remote.port);
    var req = JSON.parse(msg);

    switch(req.type){
        //---------------------------------------------------------------------
        case requestConnJson.type:
        // Another client requested a connection
        console.log("Received connection request from " + req.port + " with time = " + req.time);
        pushNewPeer(req.port, req.time);
        var resp = acceptConnJson;
        resp.time = localTime();
        console.log("Sending response: " + JSON.stringify(resp));
        sendMsg(JSON.stringify(resp), req.port);
        break;

        //---------------------------------------------------------------------
        case acceptConnJson.type:
        // Another client accepted my connection request
        console.log("Connection accepted from " + req.port + " with time = " + req.time);
        pushNewPeer(req.port, req.time);
        break;

        //---------------------------------------------------------------------
        case getPeersJson.type:
        // Another client requested list of peers
        var dbStr = JSON.stringify(db);
        sendMsg(dbStr, remote.port);
        break;

        //---------------------------------------------------------------------
        // Another client requested a specific block
        case getBlkJson.type:
        var msg = sendBlockJson;
        msg.block = blockchain.blocks[req.hash];
        msg.hash = req.hash;

        sendMsg(JSON.stringify(msg), remote.port);
        break;

        //---------------------------------------------------------------------
        // Another client requested blockchain tip
        case getTipJson.type:
        var msg = sendBlockJson;
        msg.block = blockchain.blocks[blockchain.get_tip()];
        msg.hash = blockchain.get_tip();

        sendMsg(JSON.stringify(msg), remote.port);
        break;

        //---------------------------------------------------------------------
        // Received response from getPeers
        case db.type:
        req.peers.forEach(function(peer, index) {
            // TODO: Implement a way to resend request in case a response does
            // not arrive
            if (peerIsNew(peer)) {
                requestConnection(peer);
            }
        });
        break;

        //---------------------------------------------------------------------
        // Received block
        case sendBlockJson.type:
        if (req.block) {
            var newBlock = new eth.Block;
            newBlock.from_json(req.block);
            // check if block is valid and not yet on local blockchain copy
            if ((newBlock.is_valid()) &&
                (newBlock.hash() === req.hash) &&
                (!blockchain.blocks[req.hash])) {
                // add block to blockchain
                blockchain.add(newBlock);
                // broadcast block to other peers
                broadcastBlock(newBlock);
                console.log("Blockchain len = " + Object.keys(blockchain.blocks).length);
                // if previous block is not on local blockchain copy, request previous block
                if(!blockchain.blocks[req.block.prev_hash]){
                    getBlock(req.block.prev_hash, remote.port);
                }
            }
        }
        break;

        //---------------------------------------------------------------------
        default:
        console.log("Received invalid message. Ignoring...");
        break;
    }

});

// emits when socket is ready and listening for datagram msgs
socket.on('listening',function(){
    var address = socket.address();
    var port = address.port;
    var family = address.family;
    var ipaddr = address.address;
    console.log('Listening at port ' + port);
    console.log('IP :' + ipaddr);
    console.log('IP4/IP6 : ' + family);
});

// emits when any error occurs
socket.on('error', function(error){
    console.log("Error: " + error);
    socket.close();
});

//emits after the socket is closed using socket.close();
socket.on('close',function(){
    console.log('Socket is closed !');
});

//------------- TESTS -------------\\
// getPeers
setInterval(function() {
    //console.log("getPeers");
    if (db.peers.length > 0){
        var remote = randomPeer();
        getPeers(remote);
    }
    else {
        requestConnection(REMOTE);
    }
},5000);

// getTip
setInterval(function() {
    //console.log("getTip");
    if (db.peers.length > 0){
        var remote = randomPeer();
        getTip(remote);
    }
},6000);

// newBlock
setInterval(function(){
    console.log("Discovered new block!");
    // create block
    var blk = empty_block(blockchain.get_tip());
    // add block to Blockchain
    blockchain.add(blk);
    //console.log("\n\n\n\n============================\n" + blockchain.show() + "\n=======================================\n\n\n\n");
    console.log("===> Blockchain len = " + Object.keys(blockchain.blocks).length);
    broadcastBlock(blk);
}, 10000);

// -------------- TEST FUNCTIONS ---------------- \\
function empty_block(prev_hash, extra) {
    return new eth.Block(
        localTime().toString(),
        "0000000000000000",
        extra || "00000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        prev_hash || "0000000000000000000000000000000000000000000000000000000000000000",
        eth.hash([]),
        []);
}
