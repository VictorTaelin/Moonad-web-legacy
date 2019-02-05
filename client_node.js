const udp = require('dgram');
const eth = require('./ethernal');

// Useful constants
const PORT = parseInt(process.argv[2]);
const HOST = 'localhost';
const REMOTE = parseInt(process.argv[3]);

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

// ------------- Main ------------- \\
function main() {
    if (process.argv.length != 4) {
        console.log("Usage: \"node client_node [LOCAL_PORT] [REMOTE_PORT]\"\n");
        console.log("Where LOCAL_PORT is the port used by client_node to communicate");
        console.log("with other clients and REMOTE_PORT is the port used by another");
        console.log("instance of client_node\n");
        console.log("e.g.: node client_node 5000 5001");
        process.exit();
    }

    var client = new eth.Client(HOST, PORT, HOST, REMOTE);
    client.init();
    client.run();
}
main();
