var {Pointer, Node, Net} = require("./nasic.js");
var {Lam, Var, App, Put, Dup, Ref, New, Fst, Snd, Rwt, Rfl} = require("./formality.js");

function compile(term, unsafe) {
  var level_of = {};

  function check_stratification(term, vars, level) {
    if (term instanceof Lam) {
      vars.push({name: term.name, type: "lam", uses: 0, level: level});
      check_stratification(term.body, vars, level);
      vars.pop();
    }

    else if (term instanceof App) {
      check_stratification(term.func, vars, level);
      check_stratification(term.argm, vars, level);
    }

    else if (term instanceof Var) {
      var binder = vars[vars.length - term.index - 1];
      if (!binder) {
        throw "Unbound variable.";
      }
      binder.uses += 1;
      if (binder.type === "lam" && binder.uses > 1) {
        throw "Used linear variable `" + binder.name + "` more than once.";
      }
      if (binder.type === "dup" && level - binder.level !== 1) {
        throw "Duplication variable `" + binder.name + "` should have exactly 1 surrounding box.";
      }
    }

    else if (term instanceof New) {
      check_stratification(term.val0, vars, level);
    }

    else if (term instanceof Fst) {
      check_stratification(term.term, vars, level);
    }

    else if (term instanceof Snd) {
      check_stratification(term.term, vars, level);
    }

    else if (term instanceof Put) {
      check_stratification(term.term, vars, level + 1);
    }

    else if (term instanceof Dup) {
      check_stratification(term.term, vars, level);
      vars.push({name: term.name, type: "dup", uses: 0, level: level});
      check_stratification(term.body, vars, level);
      vars.pop();
    }

    else if (term instanceof Ref) {
      check_stratification(term.term, vars, level);
    }
  }

  function build_net(term, net, var_ptrs, level) {
    if (term instanceof Lam) {
      if (term.eras) {
        var_ptrs.push(null);
        var net = build_net(term.body, net, var_ptrs, level);
        var_ptrs.pop();
        return net;
      } else {
        var lam_addr = net.alloc_node(1);
        net.link_ports(new Pointer(lam_addr, 1), new Pointer(lam_addr, 1));
        var_ptrs.push(new Pointer(lam_addr, 1));
        var body_ptr = build_net(term.body, net, var_ptrs, level);
        var_ptrs.pop();
        net.link_ports(new Pointer(lam_addr, 2), body_ptr);
        return new Pointer(lam_addr, 0);
      }
    }

    else if (term instanceof App) {
      if (term.eras) {
        return build_net(term.func, net, var_ptrs, level);
      } else {
        var app_addr = net.alloc_node(1);
        var func_ptr = build_net(term.func, net, var_ptrs, level);
        net.link_ports(new Pointer(app_addr, 0), func_ptr);
        var argm_ptr = build_net(term.argm, net, var_ptrs, level);
        net.link_ports(new Pointer(app_addr, 1), argm_ptr)
        return new Pointer(app_addr, 2);
      }
    }
    
    else if (term instanceof Var) {
      var ptr = var_ptrs[var_ptrs.length - term.index - 1];
      if (ptr === null) {
        throw "Attempted to use erased variable.";
      }
      var dups_ptr = net.enter_port(ptr);
      if (!net.enter_port(ptr) || net.enter_port(ptr).equal(ptr)) {
        return ptr;
      } else {
        var dup_addr = net.alloc_node((unsafe ? ptr.addr : level_of[ptr.to_string()]) + 2);
        net.link_ports(new Pointer(dup_addr, 0), ptr);
        net.link_ports(new Pointer(dup_addr, 1), dups_ptr);
        return new Pointer(dup_addr, 2);
      }
    }

    else if (term instanceof New) {
      return build_net(term.val0, net, var_ptrs, level);
    }

    else if (term instanceof Fst) {
      return build_net(term.term, net, var_ptrs, level);
    }

    else if (term instanceof Snd) {
      return build_net(term.term, net, var_ptrs, level);
    }
    
    else if (term instanceof Put) {
      return build_net(term.term, net, var_ptrs, level + 1);
    }

    else if (term instanceof Rwt) {
      return build_net(term.term, net, var_ptrs, level);
    }

    else if (term instanceof Rfl) {
      return build_net(term.eras, net, var_ptrs, level);
    }
    
    else if (term instanceof Dup) {
      var term_ptr = build_net(term.term, net, var_ptrs, level);
      level_of[term_ptr.to_string()] = level;
      var_ptrs.push(term_ptr);
      var body_ptr = build_net(term.body, net, var_ptrs, level);
      var_ptrs.pop();
      return body_ptr;
    }

    else if (term instanceof Ref) {
      return build_net(term.term, net, var_ptrs, level);
    }

    else {
      throw "Unsupported compilation of: " + term.to_string();
    }
  }

  if (!unsafe) {
    check_stratification(term, [], 0);
  }
  
  var net = new Net();
  var root_addr = net.alloc_node(0);
  var term_ptr = build_net(term, net, [], 0);
  net.link_ports(new Pointer(root_addr, 0), new Pointer(root_addr, 2));
  net.link_ports(new Pointer(root_addr, 1), term_ptr);
  return net;
}

function decompile(net) {
  function build_term(net, ptr, var_ptrs, dup_exit) {
    var label = net.nodes[ptr.addr].label;

    if (label === 1) {
      if (ptr.port === 0) {
        var_ptrs.push(new Pointer(ptr.addr, 1));
        var body = build_term(net, net.enter_port(new Pointer(ptr.addr, 2)), var_ptrs, dup_exit);
        var_ptrs.pop();
        return new Lam(false, "x" + var_ptrs.length, null, body);
      }

      if (ptr.port === 1) {
        for (var index = 0; index < var_ptrs.length; ++index) {
          if (var_ptrs[var_ptrs.length - index - 1].equal(ptr)) {
            return new Var(index);
          }
        }
      }

      if (ptr.port === 2) {
        var argm = build_term(net, net.enter_port(new Pointer(ptr.addr, 1)), var_ptrs, dup_exit);
        var func = build_term(net, net.enter_port(new Pointer(ptr.addr, 0)), var_ptrs, dup_exit);
        return new App(false, func, argm);
      }
    }

    else {
      if (ptr.port === 0) {
        var exit = dup_exit.pop();
        var term = build_term(net, net.enter_port(new Pointer(ptr.addr, dup_exit.head)), var_ptrs, dup_exit);
        dup_exit.push(exit);
        return term;
      } else {
        dup_exit.push(ptr.port);
        var term = build_term(net, net.enter_port(new Pointer(ptr.addr, 0)), var_ptrs, dup_exit);
        dup_exit.pop();
        return term;
      }
    }
  }
  return build_term(net, net.enter_port(new Pointer(0, 1)), [], []);
}

module.exports = {compile, decompile};
