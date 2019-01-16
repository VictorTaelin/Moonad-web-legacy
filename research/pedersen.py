from random import randrange, getrandbits

def gen_prime_number(k): # generates a `k+1` bit prime `p`
    # TODO
    p = 581697293766333808048386864819108109213
    return p

def gen_group(p): # generates a prime `q` such that `p | q-1` and a number `g`, with `1 < g < q`, of order `p`
    # TODO
    q = 3490183762598002848290321188914648655279
    g = 7
    return q, g

def HGen(k, n): # generates a hash and an increment hash function given a security parameter k and the number of blocks of the messages
    p = gen_prime_number(k+1)
    q,g = gen_group(p)
    gs = [pow(g,randrange(1,p),q) for i in range(n)] # list of random elements of the group

    def H(M): # M should be a list of bit arrays of size k; or rather, a list of bytestrings of size k/8
        n = len(gs)
        if len(M) != n:
            raise Exception("Message must have {} blocks of size {}".format(n,k))
        res = 1
        for i in range(n):
            res = (res * pow(gs[i], int.from_bytes(M[i], 'big'), q)) % q
        return res

    def IncH(M, h, j, m): # given a message M, its hash h, and a new block m at position j, computes the hash of the updated message
        g_inv = pow(gs[j], p-1, q) # computes the inverse element
        return (h * pow(g_inv, int.from_bytes(M[j], 'big'), q) * pow(gs[j], int.from_bytes(m, 'big'), q)) % q

    return H, IncH
