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

// Message Templates
var db = {'type':'addr', 'known':[]};
const getPeersJson = {'type':'getPeers', 'port':PORT};
const getBlkJson = {'type':'getBlk', 'port':PORT, 'hash':eth.empty_hash};
const getTipJson = {'type':'getBlk', 'port':PORT};

// Useful functions
function randomInt(max){
    return Math.trunc(Math.random() * max);
}

function randomPeer(){
    return db['known'][randomInt(db['known'].length)];
}

function pushNewPort(newPort){
    if ((!db['known'].includes(newPort)) && (newPort != PORT)){
        db['known'].push(newPort);
    }
}
pushNewPort(REMOTE);

// useful variables
var blockchain = new eth.Blockchain // TODO: Save blockchain in a file

// create udp socket
socket = udp.createSocket('udp4');
socket.bind(PORT);

function sendMsg(msg, port) {
    socket.send(msg, remote.port,'localhost', function(error){
        if(error){
            console.log("Error: " + error);
        }else{
            console.log(msg + ' >>>>> ' + remote.port);
        }
    });
}

// emits on new datagram msg
socket.on('message',function(msg,remote){
    console.log(msg.toString() + ' <<<<< ' + remote.port)
    var req = JSON.parse(msg);

    switch(req['type']){
        //---------------------------------------------------------------------
        case getPeersJson['type']:
        // Send peers to other nodes
        var msg = JSON.stringify(db);
        sendMsg(msg, remote.port);
        pushNewPort(remote.port);
        break;

        //---------------------------------------------------------------------
        case getBlkJson['type']:
        // send specific block to other peers
        var msg = JSON.stringify(blockchain.blocks[getBlkJson['hash']].to_json());
        sendMsg(msg, remote.port);
        pushNewPort(remote.port);
        break;

        //---------------------------------------------------------------------
        case getTipJson['type']:
        // send blockchain tip
        var msg = JSON.stringify({'tip_hash':blockchain.get_tip()});
        sendMsg(msg, remote.port);
        pushNewPort(remote.port);
        break;

        //---------------------------------------------------------------------
        case db['type']:
        req['known'].forEach(function(item, index){
            pushNewPort(item);
        });
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

setInterval(function() {
    console.log("Getting new peers...");

    //send msg
    var getPeersMsg = JSON.stringify(getPeersJson);
    var dest = randomPeer();
    socket.send(getPeersMsg, dest, 'localhost', function(error){
        if(error){
            console.log("Error: " + error);
        }else{
            console.log(getPeersMsg + ' >>>>> ' + dest);
        }
    });
},5000);
