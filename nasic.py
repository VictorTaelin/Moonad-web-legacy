class Pointer:
    def __init__(self, addr, slot):
        self.addr = addr # integer
        self.slot = slot # integer (0, 1 or 2)

    def __str__(self):
        return str(self.addr) + "abc"[self.slot]

    def __eq__(self, other):
        return other is not None and self.addr == other.addr and self.slot == other.slot

class Node:
    def __init__(self, label, ports):
        self.label = label # integer
        self.ports = ports # pointers

    def __str__(self):
        return "[" + str(self.label) + "| " + str(self.ports[0]) + " " + str(self.ports[1]) + " " + str(self.ports[2]) + "]"

class Net:
    def __init__(self):
        self.nodes = [] # nodes
        self.freed = [] # integers
        self.redex = [] # pointers

    def alloc_node(self, label):
        if len(self.freed) > 0:
            addr = self.freed.pop()
        else:
            self.nodes.append(None)
            addr = len(self.nodes) - 1
        self.nodes[addr] = Node(label, [None, None, None])
        return addr

    def free_node(self, addr):
        self.nodes[addr] = None
        self.freed.append(addr)

    def link_ports(self, a_ptr, b_ptr):
        if self.enter_port(a_ptr) == a_ptr or self.enter_port(b_ptr) == b_ptr:
            self.nodes[a_ptr.addr].ports[a_ptr.slot] = Pointer(a_ptr.addr, a_ptr.slot)
            self.nodes[b_ptr.addr].ports[b_ptr.slot] = Pointer(b_ptr.addr, b_ptr.slot)
        else:
            self.nodes[a_ptr.addr].ports[a_ptr.slot] = b_ptr
            self.nodes[b_ptr.addr].ports[b_ptr.slot] = a_ptr
        if a_ptr.slot == 0 and b_ptr.slot == 0:
            self.redex.append((a_ptr.addr, b_ptr.addr))

    def enter_port(self, ptr):
        if self.nodes[ptr.addr] is not None:
            return self.nodes[ptr.addr].ports[ptr.slot]
        else:
            return None

    def rewrite(self, (a_addr, b_addr)):
        a_node = self.nodes[a_addr]
        b_node = self.nodes[b_addr]
        if a_node.label == b_node.label:
            a_aux1_dest = self.enter_port(Pointer(a_addr, 1))
            b_aux1_dest = self.enter_port(Pointer(b_addr, 1))
            self.link_ports(a_aux1_dest, b_aux1_dest)
            a_aux2_dest = self.enter_port(Pointer(a_addr, 2))
            b_aux2_dest = self.enter_port(Pointer(b_addr, 2))
            self.link_ports(a_aux2_dest, b_aux2_dest)
        else:
            a_aux1_dest = self.enter_port(Pointer(a_addr, 1))
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
        self.free_node(a_addr)
        self.free_node(b_addr)

    def reduce(self):
        rewrite_count = 0
        while len(self.redex) > 0:
            self.rewrite(self.redex.pop())
            rewrite_count += 1
        return rewrite_count

    def __str__(self):
        text = ""
        for i in xrange(len(self.nodes)):
            text += str(i) + ": " + str(self.nodes[i]) + "\n"
        return text
