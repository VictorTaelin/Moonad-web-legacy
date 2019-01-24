// A context is an array of (name, type) tiples
class Context {
  constructor(binds) {
    this.binds = binds;
  }

  // Shifts all elements of the context
  shift(depth, inc) {
    var binds = [];
    for (var binder of this.binds) {  
      if (binder == null) {
        binds.push(null);
      } else {
        binds.push([binder[0], binder[1].shift(depth, inc)]);
      }
    }
    return new Context(binds);
  }

  // Extends the context with a term, shifting accourdingly
  extend([name, term]) {
    return new Context([[name, term]].concat(this.shift(0, 1).binds));
  }

  // Returns the type of an element given its index
  get_type(index) {
    if (index < this.binds.length) {
      return this.binds[index][1];
    }
  }

  // Returns the name of an element given its index,
  // avoiding capture by appending 's if needed
  get_name(index) {
    if (index < this.binds.length) {
      var name = this.binds[index][0];
      for (var i = 0; i < index; ++i) {
        if (this.binds[i][0] === this.binds[index][0]) {
          name += "'";
        }
      }
      return name;
    }
  }

  // Finds a term by its name, skipping a number of terms
  // (this allows the x''' syntax be used to address shadowed vars)
  find_by_name(find_name, skip) {
    for (var [name, term] of this.binds) {
      if (find_name === name) {
        if (skip > 0) {
          skip -= 1;
        } else {
          return [name, term];
        }
      }
    }
    return null;
  }

  // Pretty prints a context
  show() {
    if (this.binds.length === 0) {
      return "(empty)\n";
    } else {
      var text = "";
      for (var [name, value] of this.binds.slice(0).reverse()) {
        text += "-- " + name + " : " + value.to_string(this) + "\n";
      }
      return text;
    }
  }

  // Formats a type-mismatch error message
  show_mismatch(expect, actual, value) {
      var text = "";
      text += "ERROR: Type mismatch on " + value + ".\n";
      text += "- Expect: " + expect.to_string(this) + "\n";
      text += "- Actual: " + actual.to_string(this) + "\n"
      text += "- Context:\n" 
      text += this.show();
      return text;
  }

  check_match(expect, actual, value) {
    try {
      var checks = expect.equal(actual);
      var unsure = false;
    } catch (e) {
      var checks = false;
      var unsure = true;
    }
    if (!checks) {
      throw this.show_mismatch(expect, actual, value) + (unsure ? "\nCouldn't decide if terms are equal." : "");
    }
  }
}

// The type of types (TODO: kinding system, right now we have Type : Type)
// Syntax: Type
class Typ {
  constructor() {
  }

  to_string() {
    return "Type";
  }

  shift(depth, inc) {
    return new Typ();
  }

  subst(depth, val) {
    return new Typ();
  }

  equal(term) {
    return term.eval(false, true) instanceof Typ;
  }

  eval(full, deref) {
    return new Typ();
  }

  erase() {
    return new Typ();
  }

  check(context = new Context([])) {
    return new Typ();
  }
}

// The type of a lambda (either erased or not)
// Syntax: {x : A} B
class All {
  constructor(eras, name, bind, body) {
    this.eras = eras; // Bool (true if erased)
    this.name = name; // String (argument name)
    this.bind = bind; // Term (argument type)
    this.body = body; // Term (function body)
  }

  to_string(context = new Context([])) {
    var eras = this.eras ? "-" : "";
    var name = this.name;
    var bind = " : " + this.bind.to_string(context);
    var body = this.body.to_string(context.extend([this.name, new Var(0)]));
    return "{" + eras + name + bind + "} " + body;
  }

  shift(depth, inc) {
    var eras = this.eras;
    var name = this.name;
    var bind = this.bind.shift(depth, inc);
    var body = this.body.shift(depth + 1, inc);
    return new All(eras, name, bind, body);
  }

  subst(depth, val) {
    var eras = this.eras;
    var name = this.name;
    var bind = this.bind.subst(depth, val);
    var body = this.body.subst(depth + 1, val && val.shift(0, 1));
    return new All(eras, name, bind, body);
  }

  equal(term) {
    var term_h = term.eval(false, true);
    if (term_h instanceof All) {
      var eras = this.eras == term_h.eras;
      var bind = this.bind.equal(term_h.bind);
      var body = this.body.equal(term_h.body);
      return eras && bind && body;
    }
    return false;
  }

  eval(full, deref) {
    var eras = this.eras;
    var name = this.name;
    var bind = full ? this.bind.eval(full, deref) : this.bind;
    var body = full ? this.body.eval(full, deref) : this.body;
    return new All(eras, name, bind, body);
  }

  erase() {
    return new All(this.eras, this.name, this.bind.erase(), this.body.erase());
  }
  
  check(context = new Context([])) {
    return new Typ();
  }
}

// A lambda (either erased or not)
// Syntax: [x : A] t
class Lam {
  constructor(eras, name, bind, body) {
    this.eras = eras; // Bool (true if erased)
    this.name = name; // String (argument name)
    this.bind = bind; // Term (argument type)
    this.body = body; // Term (function body)
  }

  to_string(context = new Context([])) {
    var eras = this.eras ? "-" : "";
    var name = this.name;
    var bind = this.bind ? " : " + this.bind.to_string(context) : "";
    var body = this.body.to_string(context.extend([this.name, new Var(0)]));
    return "[" + eras + name + bind + "] " + body;
  }

  shift(depth, inc) {
    var eras = this.eras;
    var name = this.name;
    var bind = this.bind && this.bind.shift(depth, inc);
    var body = this.body.shift(depth + 1, inc);
    return new Lam(eras, name, bind, body);
  }

  subst(depth, val) {
    var eras = this.eras;
    var name = this.name;
    var bind = this.bind && this.bind.subst(depth, val);
    var body = this.body.subst(depth + 1, val && val.shift(0, 1));
    return new Lam(eras, name, bind, body);
  }

  equal(term) {
    var term_h = term.eval(false, true);
    if (term_h instanceof Lam) {
      var eras = this.eras === term_h.eras;
      var body = this.body.equal(term_h.body);
      return eras && body;
    }
    return false;
  }

  eval(full, deref) {
    var eras = this.eras;
    var name = this.name;
    var bind = full ? this.bind && this.bind.eval(full, deref) : this.bind;
    var body = full ? this.body.eval(full, deref) : this.body;
    return new Lam(eras, name, bind, body);
  }

  erase() {
    if (this.eras) {
      return this.body.erase().subst(0, null);
    } else {
      return new Lam(this.eras, this.name, null, this.body.erase());
    }
  }

  check(context = new Context([])) {
    if (this.bind === null) {
      throw "Can't infer non-annotated lambda. Context:\n" + context.show();
    } else {
      var body_t = this.body.check(context.extend([this.name, this.bind.shift(0, 1)]));
      return new All(this.eras, this.name, this.bind, body_t);
    }
  }
}

// An application
// Syntax: (f x y z ...)
class App {
  constructor(eras, func, argm) {
    this.eras = eras; // Bool (true if erased)
    this.func = func; // Term (the function)
    this.argm = argm; // Term (the argument)
  }

  to_string(context = new Context([])) {
    var text = ")";
    var self = this;
    while (self instanceof App) {
      text = " " + (self.eras ? "-" : "") + self.argm.to_string(context) + text;
      self = self.func;
    }
    return "(" + self.to_string(context) + text;
  }

  shift(depth, inc) {
    var eras = this.eras;
    var func = this.func.shift(depth, inc);
    var argm = this.argm.shift(depth, inc);
    return new App(eras, func, argm);
  }

  subst(depth, val) {
    var eras = this.eras;
    var func = this.func.subst(depth, val);
    var argm = this.argm.subst(depth, val);
    return new App(eras, func, argm);
  }

  equal(term) {
    if (term instanceof App && this.func.equal(term.func) && this.argm.equal(term.argm)) {
      return true;
    } else {
      var func_h = this.func.eval(false, true);
      if (func_h instanceof Lam) {
        return func_h.body.subst(0, this.argm).equal(term);
      } else {
        var term_h = term.eval(false, true);
        if (term_h instanceof App) {
          var eras = this.eras === term_h.eras;
          var func = this.func.equal(term_h.func);
          var argm = this.argm.equal(term_h.argm);
          return eras && func && argm;
        } else {
          return false;
        }
      }
    }
  }

  eval(full, deref) {
    var func_h = this.func.eval(false, true);
    if (func_h instanceof Lam) {
      return func_h.body.subst(0, this.argm).eval(full, deref);
    } else {
      var eras = this.eras;
      var func = full ? func_h.eval(full, deref) : func_h;
      var argm = full ? this.argm.eval(full, deref) : this.argm;
      return new App(eras, func, argm);
    }
  }

  erase() {
    if (this.eras) {
      return this.func.erase();
    } else {
      return new App(this.eras, this.func.erase(), this.argm.erase());
    }
  }

  check(context = new Context([])) {
    var func_t = this.func.check(context).eval(false, true);
    var argm_t = this.argm.check(context);
    if (!(func_t instanceof All)) {
      throw "Non-function application on `" + this.to_string(context) + "`.\n- Context:\n" + context.show();
    }
    if (func_t.eras !== this.eras) {
      throw "Mismatched erasure on " + this.to_string(context) + ".";
    }
    var expect = func_t.bind;
    var actual = argm_t;
    context.check_match(expect, actual, "application: " + this.to_string(context));
    return func_t.body.subst(0, this.argm);
  }
}

// A bruijn-indexed variable
// Syntax: (a string representing its name)
class Var {
  constructor(index) {
    this.index = index; // Number
  }

  to_string(context = new Context([])) {
    return context.get_name(this.index) || "#" + this.index;
  }

  shift(depth, inc) {
    return new Var(this.index < depth ? this.index : this.index + inc);
  }

  subst(depth, val) {
    if (depth === this.index) {
      if (val === null) {
        throw "Use of erased variable.";
      } else {
        return val;
      }
    }
    return new Var(this.index - (this.index > depth ? 1 : 0));
  }

  equal(term) {
    var term_h = term.eval(false, true);
    return term_h instanceof Var && this.index === term_h.index;
  }

  eval(full, deref) {
    return new Var(this.index);
  }

  erase() {
    return new Var(this.index);
  }

  check(context = new Context([])) {
    return context.get_type(this.index);
  }
}

class Slf {
  constructor(name, body) {
    this.name = name;
    this.body = body;
  }

  to_string(context = new Context([])) {
    return "@ " + this.name + " = " + this.body.to_string(context.extend([this.name, new Var(0)]));
  }

  shift(depth, inc) {
    return new Slf(this.name, this.body.shift(depth + 1, inc));
  }

  subst(depth, val) {
    return new Slf(this.name, this.body.subst(depth + 1, val && val.shift(0, 1)));
  }

  equal(body) {
    var body_h = body.eval(false, true);
    return body_h instanceof Slf && this.body.equal(body_h.body);
  }

  eval(full, deref) {
    return new Slf(this.name, this.body.eval(full, deref));
  }

  erase() {
    return this.body.erase();
  }

  check(context = new Context([])) {
    return this.body.check(context.extend([this.name, this.shift(0, 1)]));
  }
}

class New {
  constructor(type, term) {
    this.type = type;
    this.term = term;
  }

  to_string(context = new Context([])) {
    return ": " + this.type.to_string(context) + " = " + this.term.to_string(context);
  }

  shift(depth, inc) {
    return new New(this.type.shift(depth, inc), this.term.shift(depth, inc));
  }

  subst(depth, val) {
    return new New(this.type.subst(depth, val), this.term.subst(depth, val));
  }

  equal(term) {
    return this.term.equal(term);
  }

  eval(full, deref) {
    return full ? this.term.eval(full, deref) : this.term;
  }

  erase() {
    return this.term.erase();
  }

  check(context = new Context([])) {
    var type_h = this.type.eval(false, true);
    if (!(type_h instanceof Slf)) {
      throw "TODO";
    }
    var term_t = this.term.check(context);
    context.check_match(type_h.body.subst(0, this.term), term_t, "TODO");
    return this.type;
  }
}

class Ins {
  constructor(term) {
    this.term = term;
  }

  to_string(context = new Context([])) {
    return "~ " + this.term.to_string(context);
  }

  shift(depth, inc) {
    return new Ins(this.term.shift(depth, inc));
  }

  subst(depth, val) {
    return new Ins(this.term.subst(depth, val));
  }

  equal(term) {
    return this.term.equal(term);
  }

  eval(full, deref) {
    return full ? this.term.eval(full, deref) : this.term.eval(full, deref);
  }

  erase() {
    return this.term.erase();
  }

  check(context = new Context([])) {
    var term_t = this.term.check(context).eval(false, true);
    if (!(term_t instanceof Slf)) {
      throw "TODO";
    }
    return term_t.body.subst(0, this.term);
  }
}

// A reference to a term. This is used to preserve names and cache types.
class Ref {
  constructor(name, term, clos) {
    this.name = name; // String
    this.term = term; // Term
    this.clos = clos; // Bool
    this.type = null; // Maybe Term
  }

  to_string(context = new Context([])) {
    return this.name;
  }

  shift(depth, inc) {
    return this.clos ? this : new Ref(this.name, this.term.shift(depth, inc));
  }

  subst(depth, val) {
    return this.clos ? this : new Ref(this.name, this.term.subst(depth, val));
  }

  equal(term) {
    var term_h = term.eval(false, false);
    if (term_h instanceof Ref && term_h.name === this.name) {
      return true;
    } else {
      return term_h.equal(this.eval(false, true));
    }
  }

  eval(full, deref) {
    return deref ? this.term.eval(full, deref) : this;
  }

  erase() {
    return this.term.erase();
  }

  check(context = new Context([])) {
    if (!this.type) {
      this.type = this.term.check(context);
    }
    return this.type;
  }
}

// A temporary placeholder for to-be-defined references.
class Tmp {
  constructor(term) {
    this.term = term;
  }

  to_string(context = new Context([])) {
    return this.term.to_string(context);
  }

  shift(depth, inc) {
    return new Tmp(this.term && this.term.shift(depth, inc));
  }

  subst(depth, val) {
    return new Tmp(this.term && this.term.subst(depth, val));
  }

  equal(term) {
    return this.term.equal(term);
  }

  eval(full, deref) {
    return this.term.eval(full, deref);
  }

  erase() {
    return this.term.erase();
  }

  check(context = new Context([])) {
    return this.term.check(context);
  }
}

function parse(code) {
  var index = 0;
  var unbound_refs = [];

  function is_space(char) {
    return char === " " || char === "\t" || char === "\n";
  }

  function is_name_char(char) {
    return "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_.&".indexOf(char) !== -1;
  }

  function skip_spaces() {
    while (index < code.length && is_space(code[index])) {
      index += 1;
    }
    return index;
  }

  function match(string) {
    skip_spaces();
    var sliced = code.slice(index, index + string.length);
    if (sliced === string) {
      index += string.length;
      return true;
    }
    return false;
  }

  function error(text) {
    text += "This is the relevant code:\n\n<<<";
    text += code.slice(index - 64, index) + "<<<HERE>>>";
    text += code.slice(index, index + 64) + ">>>";
    throw text;
  }

  function parse_exact(string) {
    if (!match(string)) {
      error("Parse error, expected '" + string + "'.\n");
    }
  }

  function parse_name() {
    skip_spaces();
    var name = "";
    while (index < code.length && is_name_char(code[index])) {
      name = name + code[index];
      index += 1;
    }
    return name;
  }

  function parse_term(context) {
    // Comment
    if (match("--")) {
      while (index < code.length && code[index] !== "\n") {
        index += 1;
      }
      return parse_term(context);
    }

    // Application
    else if (match("(")) {
      var func = parse_term(context);
      while (index < code.length && !match(")")) {
        var eras = match("-");
        var argm = parse_term(context);
        var func = new App(eras, func, argm);
        skip_spaces();
      }
      return func;
    }

    // Type
    else if (match("Type")) {
      return new Typ();
    }

    // Forall
    else if (match("{")) {
      var eras = match("-");
      var name = parse_name();
      var skip = parse_exact(":");
      var bind = parse_term(context);
      var skip = parse_exact("}");
      var body = parse_term(context.extend([name, new Var(0)]));
      return new All(eras, name, bind, body);
    }

    // Lambda
    else if (match("[")) {
      var eras = match("-");
      var name = parse_name();
      var bind = match(":") ? parse_term(context) : null;
      var skip = parse_exact("]");
      var body = parse_term(context.extend([name, new Var(0)]));
      return new Lam(eras, name, bind, body);
    }

    // Slf
    else if (match("@")) {
      var name = parse_name(context);
      var skip = parse_exact("=");
      var body = parse_term(context.extend([name, new Var(0)]));
      return new Slf(name, body);
    }

    // New
    else if (match(":")) {
      var type = parse_term(context);
      var skip = parse_exact("=");
      var term = parse_term(context);
      return new New(type, term);
    }

    // Ins
    else if (match("~")) {
      var term = parse_term(context);
      return new Ins(term);
    }

    // Definition
    else if (match("def")) {
      var name = parse_name();
      var term = parse_term(context);
      var tref = new Ref(name, term, true)
      var body = parse_term(context.extend([name, tref.shift(0, 1)]));
      for (var i = 0; i < (unbound_refs[name] || []).length; ++i) {
        unbound_refs[name][i].term = tref;
      }
      delete unbound_refs[name];
      return body.shift(0, -1);
    }

    // Local definition
    else if (match("let")) {
      var name = parse_name();
      var term = parse_term(context);
      var body = parse_term(context.extend([name, term]));
      return body.shift(0, -1);
    }

    // Variable (named)
    else {
      var name = parse_name();
      var skip = 0;
      while (match("'")) {
        skip += 1;
      }
      var bind = context.find_by_name(name, skip);
      if (bind) {
        return bind[1];
      }
      var term = new Tmp(null);
      if (!unbound_refs[name]) {
        unbound_refs[name] = [];
      }
      unbound_refs[name].push(term);
      return term;
    }
  }

  var term = parse_term(new Context([]));

  var unbound_names = Object.keys(unbound_refs);
  if (unbound_names.length > 0) {
    throw "Use of undefined variables: " + unbound_names.join(", ") + ".\n";
  }

  return term;
}

module.exports = {Context, Ref, Typ, All, Lam, App, Var, parse};
