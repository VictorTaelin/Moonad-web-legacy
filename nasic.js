class Pointer {
  // A Pointer consists of an addr / port pair
  constructor(addr, port) {
    this.addr = addr; // integer (index on this.nodes where the target port is)
    this.port = port; // integer (0, 1 or 2, representing the target port)
  }

  str() {
    return this.addr + 'abc'[this.port];
  }
  
  eq(other) {
    return other !== null && this.addr === other.addr && this.port === other.port;
  }
}

class Node {
  // A node consists of a label and an array with 3 ports 
  constructor(label, ports) {
    this.label = label; // integer (this node's label)
    this.ports = ports; // array with 3 pointers (this node's edges)
  }

  str() {
    return '[' + this.label + '|' + this.ports[0].str() + ' ' + this.ports[1].str() + ' ' + this.ports[2].str() + ']';
  }
}
 
class Net {
  // A net stores nodes (this.nodes), reclaimable memory addrs (this.freed) and active pairs (this.redex)
  constructor() {
    this.nodes = []; // nodes
    this.freed = []; // integers
    this.redex = []; // array of (pointers, pointer) tuples
  }

  // Allocates a new node, return its addr
  alloc_node(label) {

    // If there is reclaimable memory, use it
    if (this.freed.length > 0) {
      var addr = this.freed.pop();
    } else { // Otherwise, extend the array of nodes
      this.nodes.push(null);
      var addr = this.nodes.length - 1;
    }

    // Fill the memory with an empty node without pointers
    this.nodes[addr] = new Node(label, [null, null, null]);
    return addr;
  }

  // Deallocates a node, allowing its space to be reclaimed
  free_node(addr) {
    this.nodes[addr] = null;
    this.freed.push(addr);
  }

  // Given a pointer to a port, returns a pointer to the opposing port
  enter_port(ptr) {
    if (this.nodes[ptr.addr] !== null) {
      return this.nodes[ptr.addr].ports[ptr.port];
    } else {
      return null;
    }
  }

  // Connects two ports
  link_ports(a_ptr, b_ptr) {
    // Stores each pointer on its opposing port
    this.nodes[a_ptr.addr].ports[a_ptr.port] = b_ptr;
    this.nodes[b_ptr.addr].ports[b_ptr.port] = a_ptr;

    // If both are main ports, add this to the list of active pairs
    if (a_ptr.port === 0 && b_ptr.port === 0) {
      this.redex.push([a_ptr.addr, b_ptr.addr]);
    } 
  }

  // Disconnects a port, causing both sides to point to themselves
  unlink_port(a_ptr) {
    var b_ptr = this.enter_port(a_ptr);
    if (this.enter_port(b_ptr) === a_ptr) {
      this.nodes[a_ptr.addr].ports[a_ptr.port] = a_ptr;
      this.nodes[b_ptr.addr].ports[b_ptr.port] = b_ptr;
    }
  }

  // Rewrites an active pair
  rewrite([a_addr, b_addr]) {
    var a_node = this.nodes[a_addr];
    var b_node = this.nodes[b_addr];

    // If both nodes have the same label, connects their neighbors
    if (a_node.label === b_node.label) {
      var a_aux1_dest = this.enter_port(new Pointer(a_addr, 1));
      var b_aux1_dest = this.enter_port(new Pointer(b_addr, 1));
      this.link_ports(a_aux1_dest, b_aux1_dest);
      var a_aux2_dest = this.enter_port(new Pointer(a_addr, 2));
      var b_aux2_dest = this.enter_port(new Pointer(b_addr, 2));
      this.link_ports(a_aux2_dest, b_aux2_dest);

    // Otherwise, the nodes pass through each-other, duplicating themselves
    } else {
      var p_addr = this.alloc_node(b_node.label);
      var q_addr = this.alloc_node(b_node.label);
      var r_addr = this.alloc_node(a_node.label);
      var s_addr = this.alloc_node(a_node.label);
      this.link_ports(new Pointer(r_addr, 1), new Pointer(p_addr, 1));
      this.link_ports(new Pointer(s_addr, 1), new Pointer(p_addr, 2));
      this.link_ports(new Pointer(r_addr, 2), new Pointer(q_addr, 1));
      this.link_ports(new Pointer(s_addr, 2), new Pointer(q_addr, 2));
      this.link_ports(new Pointer(p_addr, 0), this.enter_port(new Pointer(a_addr, 1)));
      this.link_ports(new Pointer(q_addr, 0), this.enter_port(new Pointer(a_addr, 2)));
      this.link_ports(new Pointer(r_addr, 0), this.enter_port(new Pointer(b_addr, 1)));
      this.link_ports(new Pointer(s_addr, 0), this.enter_port(new Pointer(b_addr, 2)));
    }

    // Deallocates the space used by the active pair
    for (var i = 0; i < 3; i++) {
      this.unlink_port(new Pointer(a_addr, i));
      this.unlink_port(new Pointer(b_addr, i));
    }
    this.free_node(a_addr);
    this.free_node(b_addr);
  }

  // Rewrites active pairs until none is left, reducing the graph to normal form
  reduce() {
    var rewrite_count = 0;
    while (this.redex.length > 0) {
      this.rewrite(this.redex.pop());
      rewrite_count += 1;
    }
    return [this, rewrite_count];
  }

  str() {
    var text = '';
    for (var i = 0; i < this.nodes.length; i++) {
      if (this.nodes[i] !== null) {
        text += i + ': ' + this.nodes[i].str() + '\n';
      } else {
        text += i + ': ' + null + '\n';
      }
    }
    return text;
  }
}

module.exports = {Pointer, Node, Net};
