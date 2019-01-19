const udp = require('dgram');

if (process.argv.length != 4) {
    console.log("Usage: \"node client_node [LOCAL_PORT] [REMOTE_PORT]\"\n");
    console.log("Where LOCAL_PORT is the port used by client_node to communicate");
    console.log("with other clients and REMOTE_PORT is the port used by another");
    console.log("instance of client_node\n");
    console.log("e.g.: node client_node 5000 5001");
    process.exit();
}

const PORT = parseInt(process.argv[2]);
const REMOTE = parseInt(process.argv[3]);

// Message Templates
var db = {'type':'addr', 'known':[]};
const getPeers = {'type':'getPeers', 'port':PORT}
const getBlk = {'type':'getBlk', 'port':PORT}

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

// create udp socket
socket = udp.createSocket('udp4');
socket.bind(PORT);

// emits on new datagram msg
socket.on('message',function(msg,remote){
    //console.log(remote.address + ':' + remote.port +' - (' + msg.length + ' bytes) ' + msg.toString());
    console.log(msg.toString() + ' <<<<< ' + remote.port)
    var req = JSON.parse(msg);

    switch(req['type']){
        case getPeers['type']:
        var msg = JSON.stringify(db);
        socket.send(msg, remote.port,'localhost', function(error){
            if(error){
                console.log("Error: " + error);
            }else{
                console.log(msg + ' >>>>> ' + remote.port);
            }
        });
        pushNewPort(remote.port);
        break;

        case db['type']:
        req['known'].forEach(function(item, index){
            pushNewPort(item);
        });
        break;

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
    var getPeersMsg = JSON.stringify(getPeers);
    var dest = randomPeer();
    socket.send(getPeersMsg, dest, 'localhost', function(error){
        if(error){
            console.log("Error: " + error);
        }else{
            console.log(getPeersMsg + ' >>>>> ' + dest);
        }
    });
},5000);
