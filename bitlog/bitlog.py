# bitlog.py
# A Python example implementation of the bitlog blockchain protocol

from keccak import Keccak
import binascii

class BlockHeader:
    # TODO: Implement
    """
    BlockHeader
    """
    def __init__(self):
        self.version = "0"
        self.previous = "0"
        self.root = "0"
        self.time = "0"
        self.nBits = "0"
        self.nonce = "0"

    # Compute header hash
    def hash(self):
        header = [self.version,
                  self.previous,
                  self.root,
                  self.time,
                  self.nBits,
                  self.nonce]
        headerStr = "".join(header)
        bheaderStr = bytearray(headerStr)
        return binascii.hexlify(Keccak(1088, 512, bheaderStr, 0x01, 256//8))

class Block:
    # TODO: Implement
    """
    Block
    """
    def __init__(self, header):
        self.transactions = []
        self.header = header
        self.header.root = self.hash()
        self.headerHash = self.header.hash()

        # Check if block is valid
    def validate(self):
        if self.headerHash == self.header.hash():
             return True
        return False

    # Return previous block header hash
    def previous(self):
        return self.header.previous

    # Compute transactions hash
    def hash(self):
        txs = "".join(self.transactions)
        btxs = bytearray(txs)
        return binascii.hexlify(Keccak(1088, 512, btxs, 0x01, 256//8))

    def root(self):
        blk =  self.header.hash() + self.hash()
        bblk = bytearray(blk)
        return binascii.hexlify(Keccak(1088, 512, bblk, 0x01, 256//8))

    # Add transaction to block
    def add(self, transaction):
        self.transactions.append(transaction)


class Blockchain:
    # TODO: Implement
    """
    Blockchain
    """
    def __init__(self):
        self.chain = {}
        self.tip = "0"

    # Add a block to the Blockchain
    def add(self, block):
        if (self.tip == block.header.previous) and (block.validate()):
            blkRoot = block.root()
            if self.chain.has_key(blkRoot):
                print("WARNING! Collision detected!") #TODO: treat collisions
            else:
                self.chain[blkRoot] = block
                self.tip = blkRoot

    def printChain(self):
        for key in self.chain:
            print key,
            print " ---> prev: ",
            print self.chain[key].header.previous

def main():
    print("Hash testing:")
    print("Keccac \"\" hash:")
    print binascii.hexlify(Keccak(1088, 512, "", 0x01, 256//8))
    print

    blkChn = Blockchain()

    genesisH = BlockHeader()
    genesis = Block(genesisH)
    blkChn.add(genesis)

    blkH1 = BlockHeader()
    blkH1.previous = blkChn.tip
    blk1 = Block(blkH1)
    blkChn.add(blk1)

    blkH2 = BlockHeader()
    blkH2.previous = blkChn.tip
    blk2 = Block(blkH2)
    blkChn.add(blk2)

    blkChn.printChain()
    #print(blkChn.chain)

main()
