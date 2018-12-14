```
TODO:
no reduce function on formality!
instead, reduce = from_net(type, reduce_net(to_net(x)))
readback of pattern-matching is detected when a solid type is applied to something
```

## Moon: a Peer-to-Peer Operating System

**Abstract.** A purely peer-to-peer implementation of an operating system should allow online applications to operate perpetually with no downtime. Ethereum partly solved that problem in 2014, but is limited to smart-contracts. Building upon its ideas, we present the design of a complete decentralized operating system. Our low-level machine language, Nasic, is inherently parallel and adequate for reducing high-order programs efficiently, in contrast to register and stack machines. Our high-level language, Formality, is capable of exploiting Curry-Howard's isomorphism to verify security claims offline, allowing users to trust downloaded code without trusting its developers. An inductive datatype, DappSpec, is used to specify front-end user interfaces. A proof-of-work, tokenless blockchain, Bitlog, is used to aggregate and order global transactions, allowing applications to have a common back-end state. Our design is complete and final, in the sense no further updates will ever be needed, making this a self-contained, timeless specification of the operating system. To facilitate independent implementations, each module is accompanied by commented Python code.

## 1. Nasic: a parallel, low-level machine language

A very simple graph-rewrite system with only 3 symbols and 6 rules has been shown to be a universal model of computation [1]. This system is particularly interesting for its perfect computational properties. Like a Turing machine, it can be evaluated as a series of atomic, local operations with a clear cost model. Like the λ-calculus, it is inherently high-order and has a nice logical interpretation. While, from the viewpoint of *computability*, those systems are equivalent (Turing complete), from the viewpoint of *computation*, interaction combinators is arguably superior, for being confluent and inherently parallel. In other words, while the Turing machine and other classical models can always be simulated by interaction combinators with no loss of efficiency, the converse isn't true. For those reasons, Moon uses an adaptation of it, Nasic (standing for n-ary symmetric interaction combinators), as its low-level machine language. This allows its applications to run in a model that, despite being so simple, is infinitely optimizable and extremelly powerful, thus, remarkably future-proof.

### Specification

Differently from conventional machine languages, which are usually described as bytecodes, Nasic programs are described as graphs in a specific format, which includes a single type of node with 3 outgoing edges and a symbolic label. That node is depicted below in a visual notation:

(image)

Any connected arrangement of those nodes forms a valid Nasic program. For example, those are valid Nasic programs:

(image)

Notice that the position of edges is important. For example, those graphs, while isomorphic, denote two different programs:

(image)

For that reason, the ports from which edges come are named. The port at the top of the triangle is the `main` port. The one nearest to it in counter-clockwise direction is the `aux1` port. The other one is the `aux2` port.

(image)

Moreover, there are 2 computation rules:

(image)

Those rewrite rules dictate that, whenever a sub-graph matches the left side of a rule, it must be replaced by its right side. For example, the graph below:

(image)

Is rewritten as:

(image)

Because (...). Rewritteable nodes are called redexes, or active pairs. 

This completes Nasic's specification. At this point, you might be questioning if such a simple graphical system can really replace Assembly and describe arbitrary programs that range from simple calculators to entire online games and social networks. While this may not be obvious or intuitive at first, rest assured the answer is yes, as will become clear through the paper. For now, we'll shift our focus to just implementing such system, as described. 

### Implementation

In our implementation, we will represent a Net as a table, where each row represents a Node, with its label, and 3 ports, each one including a Pointer to another port. As an example, consider the following net:

(image)

This could be represented as the following table:

addr | label | port 0 | port 1 | port 2
--- | --- | --- | --- | ---
0 | 0 | addr X, port X | addr X, port X | addr X, port X
1 | 0 | addr X, port X | addr X, port X | addr X, port X
2 | 1 | addr X, port X | addr X, port X | addr X, port X
3 | 0 | addr X, port X | addr X, port X | addr X, port X

Here, we already identify all the 3 classes used by our implementation: `Pointer`, `Node` and `Net`:

```python
class Pointer:
    # A Pointer consists of an addr / port pair
    def __init__(self, addr, port):
        self.addr = addr # integer (index on self.nodes where the target port is)
        self.port = port # integer (0, 1 or 2, representing the target port)

class Node:
    # A node consists of a label and an array with 3 ports
    def __init__(self, label, ports):
        self.label = label # integer (this node's label)
        self.ports = ports # array with 3 pointers (this node's edges)

class Net:
    # A net stores nodes (self.nodes), reclaimable memory addrs (self.freed) and active pairs (self.redex)
    def __init__(self):
        self.nodes = [] # nodes
        self.freed = [] # integers
        self.redex = [] # array of (pointer, pointer) tuples
```

In addition to the table of nodes, the `Net` class also includes two additional arrays, `freed`, which will keep track of reclaimable memory, and `redex`, which will keep track of active pairs. We can, now, create an empty Net as follows:

```python
net = Net()
```

In order to add nodes to it, we need an allocation function. For that, we can extend the `Net` class with a new method:

```python
    # Allocates a new node, return its addr
    def alloc_node(self, label):

        # If there is reclaimable memory, use it
        if len(self.freed) > 0:
            addr = self.freed.pop()

        # Otherwise, extend the array of nodes
        else:
            self.nodes.append(None)
            addr = len(self.nodes) - 1

        # Fill the memory with an empty node without pointers
        self.nodes[addr] = Node(label, [None, None, None])
        return addr
```

That function allocates space for a new node, reusing freed memory if possible, and returning the allocated addr. We can also implement a deallocation function, which erases a node and marks its memory as free:

```python
    # Deallocates a node, allowing its space to be reclaimed
    def free_node(self, addr):
        self.nodes[addr] = None
        self.freed.append(addr)
```

We are now able to create the 4 nodes of our graph:

```python
net.alloc_node(1)
net.alloc_node(2)
net.alloc_node(1)
net.alloc_node(1)
```

Now, we must wire those nodes. For that, we extend `Net` with two other functions:

```python
    # Given a pointer to a port, returns a pointer to the opposing port
    def enter_port(self, ptr):
        if self.nodes[ptr.addr] is not None:
            return self.nodes[ptr.addr].ports[ptr.port]
        else:
            return None

    # Connects two ports
    def link_ports(self, a_ptr, b_ptr):

        # If one of the ports connects to itself, then connect the other to itself too
        if self.enter_port(a_ptr) == a_ptr or self.enter_port(b_ptr) == b_ptr:
            self.nodes[a_ptr.addr].ports[a_ptr.port] = Pointer(a_ptr.addr, a_ptr.port)
            self.nodes[b_ptr.addr].ports[b_ptr.port] = Pointer(b_ptr.addr, b_ptr.port)

        # Otherwise, connect both ports to each-other
        else:
            self.nodes[a_ptr.addr].ports[a_ptr.port] = b_ptr
            self.nodes[b_ptr.addr].ports[b_ptr.port] = a_ptr

        # If both are main ports, add this to the list of active pairs
        if a_ptr.port == 0 and b_ptr.port == 0:
            self.redex.append((a_ptr.addr, b_ptr.addr))
```

The `enter_port` function receives a pointer and returns a pointer to the opposing port. The `link_ports` function receives two pointers and connects their ports. Doing that is simple: we just need to store the first pointer on the second port, and the second pointer on the first port. There is a problem with this approach, though: if a port is connected to itself, this could leave the graph in an illegal state where a port points to another port that doesn't point back to it. To avoid that, we explicitly detect such case, performing the correct wiring. Now we're able to complete the graph above as follows:

```python
net.link_ports(Pointer(0,0), Pointer(0,2))
net.link_ports(Pointer(0,1), Pointer(3,2))
net.link_ports(Pointer(1,0), Pointer(2,0))
net.link_ports(Pointer(1,1), Pointer(3,0))
net.link_ports(Pointer(1,2), Pointer(3,1))
net.link_ports(Pointer(2,1), Pointer(2,2))
```

Now our graph is fully constructed. To complete our implementation, we just extend `Net` again with two more functions:


```python
    # Rewrites an active pair
    def rewrite(self, (a_addr, b_addr)):
        a_node = self.nodes[a_addr]
        b_node = self.nodes[b_addr]

        # If both nodes have the same label, connects their neighbors (annihilation)
        if a_node.label == b_node.label:
            a_aux1_dest = self.enter_port(Pointer(a_addr, 1))
            b_aux1_dest = self.enter_port(Pointer(b_addr, 1))
            self.link_ports(a_aux1_dest, b_aux1_dest)
            a_aux2_dest = self.enter_port(Pointer(a_addr, 2))
            b_aux2_dest = self.enter_port(Pointer(b_addr, 2))
            self.link_ports(a_aux2_dest, b_aux2_dest)

        # Otherwise, the nodes pass through each-other, duplicating themselves (commutation)
        else:
            p_addr = self.alloc_node(b_node.label)
            q_addr = self.alloc_node(b_node.label)
            r_addr = self.alloc_node(a_node.label)
            s_addr = self.alloc_node(a_node.label)
            self.link_ports(Pointer(r_addr, 1), Pointer(p_addr, 1))
            self.link_ports(Pointer(s_addr, 1), Pointer(p_addr, 2))
            self.link_ports(Pointer(r_addr, 2), Pointer(q_addr, 1))
            self.link_ports(Pointer(s_addr, 2), Pointer(q_addr, 2))
            self.link_ports(Pointer(p_addr, 0), self.enter_port(Pointer(a_addr, 1)))
            self.link_ports(Pointer(q_addr, 0), self.enter_port(Pointer(a_addr, 2)))
            self.link_ports(Pointer(r_addr, 0), self.enter_port(Pointer(b_addr, 1)))
            self.link_ports(Pointer(s_addr, 0), self.enter_port(Pointer(b_addr, 2)))

        # Deallocates the space used by the active pair
        self.free_node(a_addr)
        self.free_node(b_addr)

    # Rewrites active pairs until none is left, reducing the graph to normal form
    def reduce(self):
        rewrite_count = 0
        while len(self.redex) > 0:
            self.rewrite(self.redex.pop())
            rewrite_count += 1
        return rewrite_count
```

The first function, `rewrite`, receives an active pair and rewrites it, using the rules we presented previously. The second function, `reduce`, merely applies `rewrite` over and over to active pairs until there is no more work to be done, returning the computational cost of evaluating this program (net). Together, they form the heart of our algorithm, encapsulating the fundamental rules of computation, annihilation and commutation. The first rule allows separate pieces of information to interact, capturing different phenomena such as functions, datatypes and pattern-matching. The second rule allows sub-graphs to be duplicated at will, capturing phenomena such as loops and recursion. Parallelism, while absent from this implementation, is captured by the fact redexes could be rewritten simultaneously. Memory allocation and garbage-collection are captured by the fact nodes are incrementally freed when subgraphs "go out of scope". We're now able to evaluate our input program (net) as follows:

```
net.reduce()
```

As a result, our `net` will now contain the following graph:

(image)

Which is the normal form of the input. This completes the reference implementation of Moon's low-level machine language, Nasic. An executable example is available at [`nasic.py`](nasic.py).

### Performance considerations

While we've presented a complete Python implementation, it is clearly not the fastest one. In other of our implementations, we've observed remarkable performance characteristics. In ideal cases, Nasic managed to beat mature functional compilers such as GHC by orders of magnitude, due to optimal reductions and runtime fusion, which are unique to it. Even in worst cases, it didn't stand far behind in raw pattern-matches per second. Since those were naive implementations, though, there is still a lot of room for improvements. Nasic's structure makes it adequate for massively parallel architectures such as the GPU, which we did not fully explore yet. With proper miniaturization such as FPGAs and ASICs, we could have native Nasic processors as alternative for classical computer architectures. We leave it for client developers to creatively optimize their Nasic implementations as much as possible. 

## 2. Formality: a high-level language for programs and proofs

types as a language of specifications

programs as mathematical proofs

### Description

### Implementation

## 3. DappSpec: a specification format for decentralized applications

```haskell
data Uint : Type
| O : (x : Uint) -> Uint
| I : (x : Uint) -> Uint
| Z : Uint

data List<A : Type> : Type
| cons : (x : A, xs : List) -> List
| nil  : List

data Element : Type
| circle : (x : Uint, y : Uint, r : Uint) -> Element
| square : (x : Uint, y : Uint, r : Uint) -> Element

let Document List<Element>

data LocalEvent : Type
| MouseClick : (x : Uint, y : Uint) -> LocalEvent
| Keypress   : (k : Uint)           -> LocalEvent

data App : Type
| new : 
  ( LocalState     : Type
  , local_inistate : LocalState
  , local_transact : (event : LocalEvent, state : LocalState) -> LocalState
  , render         : (state : LocalState) -> Document)
  -> App
```

## 4. Bitlog: a token-less blockchain for global transactions

## References

[1] https://pdfs.semanticscholar.org/6cfe/09aa6e5da6ce98077b7a048cb1badd78cc76.pdf
