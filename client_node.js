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
blockchain.add(empty_block());
var socket = udp.createSocket('udp4');
socket.bind(PORT);

// Peer Database
var db = {'type':'addr', 'known':[]};

// Message Templates
const getPeersJson = {'type':'getPeers', 'port':PORT};
const getBlkJson = {'type':'getBlk', 'port':PORT, 'hash':eth.empty_hash};
const getTipJson = {'type':'getTip', 'port':PORT};
const sendBlockJson = {'type':'block', 'port':PORT, 'hash':eth.empty_hash, 'block':empty_block()};

// Useful functions
function randomInt(max){
    return Math.trunc(Math.random() * max);
}

function randomPeer(){
    return db.known[randomInt(db.known.length)];
}

function pushNewPort(newPort){
    if ((!db.known.includes(newPort)) && (newPort != PORT)){
        db.known.push(newPort);
        console.log(db);
    }
}
pushNewPort(REMOTE);

function sendMsg(msg, port) {
    socket.send(msg, port,'localhost', function(error){
        if(error){
            console.log("Error: " + error);
        }else{
            //console.log(msg + ' >>>>> ' + port);
        }
    });
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
    db.known.forEach(function(peer, index) {
        sendMsg(msg, peer);
    });
}

function broadcastBlock(blk){
    var msg = sendBlockJson;
    msg.hash = blk.hash();
    msg.block = blk;
    broadcast(JSON.stringify(msg));
}

// Event Handlers
// emits on new datagram msg
socket.on('message',function(msg, remote){
    //console.log(msg.toString() + ' <<<<< ' + remote.port);
    var req = JSON.parse(msg);

    switch(req.type){
        //---------------------------------------------------------------------
        case getPeersJson.type:
        // Another client requested list of peers
        var dbStr = JSON.stringify(db);
        sendMsg(dbStr, remote.port);
        pushNewPort(remote.port);
        break;

        //---------------------------------------------------------------------
        // Another client requested a specific block
        case getBlkJson.type:
        var msg = sendBlockJson;
        msg.block = blockchain.blocks[req.hash];
        msg.hash = req.hash;

        sendMsg(JSON.stringify(msg), remote.port);
        pushNewPort(remote.port);
        break;

        //---------------------------------------------------------------------
        // Another client requested blockchain tip
        case getTipJson.type:
        var msg = sendBlockJson;
        msg.block = blockchain.blocks[blockchain.get_tip()];
        msg.hash = blockchain.get_tip();

        sendMsg(JSON.stringify(msg), remote.port);
        pushNewPort(remote.port);
        break;

        //---------------------------------------------------------------------
        // Received response from getPeers
        case db.type:
        req['known'].forEach(function(item, index){
            pushNewPort(item);
        });
        break;

        //---------------------------------------------------------------------
        // Received block
        case sendBlockJson.type:
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
    var remote = randomPeer();
    getPeers(remote);
},5000);

// getTip
setInterval(function() {
    //console.log("getTip");
    var remote = randomPeer();
    getTip(remote);
},6000);

// getBlock
/*setInterval(function() {
    console.log("getBlock");
    var remote = randomPeer();
    getBlock(remote);
},7000);*/

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

/*setInterval(function(){
    console.log("Blockchain len = " + Object.keys(blockchain.blocks).length);
}, 2000);*/

// -------------- TEST FUNCTIONS ---------------- \\
function empty_block(prev_hash, extra) {
    return new eth.Block(
        "0000000000000000",
        "0000000000000000",
        extra || "00000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        prev_hash || "0000000000000000000000000000000000000000000000000000000000000000",
        eth.hash([]),
        []);
}
