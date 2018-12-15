class Pointer:
    # A Pointer consists of an addr / port pair
    def __init__(self, addr, port):
        self.addr = addr # integer (index on self.nodes where the target port is)
        self.port = port # integer (0, 1 or 2, representing the target port)

    def __str__(self):
        return str(self.addr) + "abc"[self.port]

    def __eq__(self, other):
        return other is not None and self.addr == other.addr and self.port == other.port

class Node:
    # A node consists of a label and an array with 3 ports
    def __init__(self, label, ports):
        self.label = label # integer (this node's label)
        self.ports = ports # array with 3 pointers (this node's edges)

    def __str__(self):
        return "[" + str(self.label) + "| " + str(self.ports[0]) + " " + str(self.ports[1]) + " " + str(self.ports[2]) + "]"

class Net:
    # A net stores nodes (self.nodes), reclaimable memory addrs (self.freed) and active pairs (self.redex)
    def __init__(self):
        self.nodes = [] # nodes
        self.freed = [] # integers
        self.redex = [] # array of (pointer, pointer) tuples

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

    # Deallocates a node, allowing its space to be reclaimed
    def free_node(self, addr):
        self.nodes[addr] = None
        self.freed.append(addr)

    # Given a pointer to a port, returns a pointer to the opposing port
    def enter_port(self, ptr):
        if self.nodes[ptr.addr] is not None:
            return self.nodes[ptr.addr].ports[ptr.port]
        else:
            return None

    # Connects two ports
    def link_ports(self, a_ptr, b_ptr):
        # Stores each pointer on its opposing port
        self.nodes[a_ptr.addr].ports[a_ptr.port] = b_ptr
        self.nodes[b_ptr.addr].ports[b_ptr.port] = a_ptr

        # If both are main ports, add this to the list of active pairs
        if a_ptr.port == 0 and b_ptr.port == 0:
            self.redex.append((a_ptr.addr, b_ptr.addr))

    # Disconnects a port, causing both sides to point to themselves
    def unlink_port(self, a_ptr):
        b_ptr = self.enter_port(a_ptr)
        if self.enter_port(b_ptr) == a_ptr:
            self.nodes[a_ptr.addr].ports[a_ptr.port] = a_ptr
            self.nodes[b_ptr.addr].ports[b_ptr.port] = b_ptr

    # Rewrites an active pair
    def rewrite(self, (a_addr, b_addr)):
        a_node = self.nodes[a_addr]
        b_node = self.nodes[b_addr]

        # If both nodes have the same label, connects their neighbors
        if a_node.label == b_node.label:
            a_aux1_dest = self.enter_port(Pointer(a_addr, 1))
            b_aux1_dest = self.enter_port(Pointer(b_addr, 1))
            self.link_ports(a_aux1_dest, b_aux1_dest)
            a_aux2_dest = self.enter_port(Pointer(a_addr, 2))
            b_aux2_dest = self.enter_port(Pointer(b_addr, 2))
            self.link_ports(a_aux2_dest, b_aux2_dest)

        # Otherwise, the nodes pass through each-other, duplicating themselves
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
        for p in xrange(3):
            self.unlink_port(Pointer(a_addr, p))
            self.unlink_port(Pointer(b_addr, p))
        self.free_node(a_addr)
        self.free_node(b_addr)

    # Rewrites active pairs until none is left, reducing the graph to normal form
    def reduce(self):
        rewrite_count = 0
        while len(self.redex) > 0:
            self.rewrite(self.redex.pop())
            rewrite_count += 1
        return (rewrite_count, self)

    def __str__(self):
        text = ""
        for i in xrange(len(self.nodes)):
            text += str(i) + ": " + str(self.nodes[i]) + "\n"
        return text

# Runs the paper example
def run_example():
    net = Net()
    net.alloc_node(1)
    net.alloc_node(2)
    net.alloc_node(1)
    net.alloc_node(1)
    net.link_ports(Pointer(0,0), Pointer(0,2))
    net.link_ports(Pointer(0,1), Pointer(3,2))
    net.link_ports(Pointer(1,0), Pointer(2,0))
    net.link_ports(Pointer(1,1), Pointer(3,0))
    net.link_ports(Pointer(1,2), Pointer(3,1))
    net.link_ports(Pointer(2,1), Pointer(2,2))
    print "Input:"
    print net
    rewrites = net.reduce()[0]
    print "Output:"
    print net
    print "Rewrites: " + str(rewrites)

run_example()
