keccak256 = require("./keccak");

function hash(strings) {
    return keccak256(strings.join(""));
};

const empty_hash = "0000000000000000000000000000000000000000000000000000000000000000"

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

    test() {
        console.log("works");
    };
}

function main() {
    var blockchain = new Blockchain();

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
    hash: hash,
    empty_hash: empty_hash,
}


// test();
//main();
