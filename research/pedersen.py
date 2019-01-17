from random import randrange, getrandbits

def is_prime(n, k=128):
    # Test if n is not even.
    # But care, 2 is prime !
    if n == 2 or n == 3:
        return True
    if n <= 1 or n % 2 == 0:
        return False
    # find r and s
    s = 0
    r = n - 1
    while r & 1 == 0:
        s += 1
        r //= 2
    # do k tests
    for _ in range(k):
        a = randrange(2, n - 1)
        x = pow(a, r, n)
        if x != 1 and x != n - 1:
            j = 1
            while j < s and x != n - 1:
                x = pow(x, 2, n)
                if x == 1:
                    return False
                j += 1
            if x != n - 1:
                return False

    return True

def gen_prime_candidate(length):
    # generate random bits
    p = getrandbits(length)
    # apply a mask to set MSB and LSB to 1
    p |= (1 << length - 1) | 1

    return p

def gen_prime_number(length=1024):
    p = 4
    # keep generating while the primality test fail
    while not is_prime(p, 128):
        p = gen_prime_candidate(length)
    return p

# Generates a prime q such that p | q-1 and an element g of order p of the multiplicative group of q
def gen_group(p):
    q = 1+2*p
    while not is_prime(q, 128):
        q += p
    g = 2
    while not pow(g,p,q) == 1:
        g += 1
    return q, g

# Generates a hash and an increment hash function given a security parameter k and the number n of blocks of the messages to be hashed
def gen_hash(k, n):
    p = gen_prime_number(k+1)
    q,g = gen_group(p)
    gs = [pow(g,randrange(1,p),q) for i in range(n)] # list of random elements of the group

    # Hash function. M should be a list of bit arrays of size k; or rather, a list of bytestrings of size k/8
    def H(M):
        n = len(gs)
        if len(M) != n:
            raise Exception("Message must have {} blocks of size {}".format(n,k))
        res = 1
        for i in range(n):
            res = (res * pow(gs[i], int.from_bytes(M[i], 'big'), q)) % q
        return res

    # Increment hash function. Given a message M, its hash h, and a new block m at position j, computes the hash of the updated message
    def IncH(M, h, j, m):
        g_inv = pow(gs[j], p-1, q) # computes the inverse element
        return (h * pow(g_inv, int.from_bytes(M[j], 'big'), q) * pow(gs[j], int.from_bytes(m, 'big'), q)) % q

    return H, IncH
