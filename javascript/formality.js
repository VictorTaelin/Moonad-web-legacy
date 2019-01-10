class Context {
  constructor(binds) {
    this.binds = binds;
  }

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

  extend([name, term]) {
    return new Context([[name, term ? term.shift(0, 1) : new Var(0)]].concat(this.shift(0, 1).binds));
  }

  get_type(index) {
    if (index < this.binds.length) {
      return this.binds[index][1];
    }
  }

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

  find_by_name(find_name, skip, only_data) {
    for (var [name, term] of this.binds) {
      if (find_name === name) {
        if (only_data && !(term.eval(false) instanceof Idt)) {
        } else if (skip > 0) {
          skip -= 1;
        } else {
          return [name, term];
        }
      }
    }
    return null;
  }

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

  show_mismatch(expect, actual, value) {
      var text = "";
      text += "Type mismatch on " + value + ".\n";
      text += "- Expect: " + expect.to_string(this) + "\n";
      text += "- Actual: " + actual.to_string(this) + "\n"
      text += "- Context:\n" + this.show();
      return text;
  }
}

class Nik {
  constructor(name, term) {
    this.name = name;
    this.term = term;
  }

  to_string(context = new Context([])) {
    return this.name;
  }

  shift(depth, inc) {
    return new Nik(this.name, this.term.shift(depth, inc));
  }

  subst(depth, val) {
    return new Nik(this.name, this.term.subst(depth, val));
  }

  uses(depth) {
    return this.term.uses(depth);
  }

  equal(other) {
    return this.term.equal(other);
  }

  eval(erase) {
    return this.term.eval(erase);
  }

  check(context = new Context([])) {
    return this.term.check(context);
  }
}

class Typ {
  constructor() {
  }

  to_string(context = new Context([])) {
    return "Type";
  }

  shift(depth, inc) {
    return new Typ();
  }

  subst(depth, val) {
    return new Typ();
  }

  uses(depth) {
    return 0;
  }

  equal(other) {
    return other instanceof Typ;
  }

  eval(erase) {
    return new Typ();
  }
  
  check(context = new Context([])) {
    return new Typ();
  }
}

class All {
  constructor(eras, name, bind, body) {
    this.eras = eras;
    this.name = name;
    this.bind = bind;
    this.body = body;
  }

  to_string(context = new Context([])) {
    var eras = this.eras ? "-" : "";
    var name = this.name;
    var bind = " : " + this.bind.to_string(context);
    var body = this.body.to_string(context.extend([this.name, this.bind]));
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

  uses(depth) {
    var bind = this.bind.uses(depth);
    var body = this.body.uses(depth + 1);
    return bind + body;
  }

  equal(other) {
    if (other instanceof All) {
      var eras = this.eras == other.eras;
      var bind = this.bind.equal(other.bind);
      var body = this.body.equal(other.body);
      return eras && bind && body;
    }
    return false;
  }

  eval(erase) {
    var eras = this.eras;
    var name = this.name;
    var bind = this.bind.eval(erase);
    var body = this.body.eval(erase);
    return new All(eras, name, bind, body);
  }

  check(context = new Context([])) {
    var bind_v = this.bind;
    var bind_t = this.bind.check(context);
    var body_t = this.body.check(context.extend([this.name, bind_v]));
    if (!bind_t.eval(true).equal(new Typ()) || !body_t.eval(true).equal(new Typ())) {
      throw "Forall not a type. Context:\n" + context.show();
    }
    return new Typ();
  }
}

class Lam {
  constructor(eras, name, bind, body) {
    this.eras = eras;
    this.name = name;
    this.bind = bind;
    this.body = body;
  }

  to_string(context = new Context([])) {
      var eras = this.eras ? "-" : "";
      var name = this.name;
      var bind = this.bind ? " : " + this.bind.to_string(context) : "";
      var body = this.body.to_string(context.extend([this.name, null]));
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

  uses(depth) {
    var bind = this.bind.uses(depth);
    var body = this.body.uses(depth + 1);
    return bind + body;
  }

  equal(other) {
    if (other instanceof Lam) {
      var eras = this.eras === other.eras;
      var body = this.body.equal(other.body);
      return eras && body;
    }
    return false;
  }

  eval(erase) {
    if (erase && this.eras) {
      return this.body.eval(erase).subst(0, null);
    } else {
      var eras = this.eras;
      var name = this.name;
      var bind = erase ? null : this.bind.eval(erase);
      var body = this.body.eval(erase);
      return new Lam(eras, name, bind, body);
    }
  }

  check(context = new Context([])) {
    if (this.bind === null) {
      throw "Can't infer non-annotated lambda. Context:" + context.show();
    } else {
      var bind_v = this.bind;
      var bind_t = this.bind.check(context);
      var body_t = this.body.check(context.extend([this.name, bind_v]));
      if (!bind_t.eval(true).equal(new Typ())) {
        throw "Function type not a type. Context:" + context.show();
      }
      return new All(this.eras, this.name, bind_v, body_t);
    }
  }
}

class App {
  constructor(eras, func, argm) {
    this.eras = eras;
    this.func = func;
    this.argm = argm;
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

  uses(depth) {
    return this.func.uses(depth) + this.argm.uses(depth);
  }

  equal(other) {
    if (other instanceof App) { 
      var eras = this.eras == other.eras;
      var func = this.func.equal(other.func);
      var argm = this.argm.equal(other.argm);
      return eras && func && argm;
    }
    return false;
  }

  eval(erase) {
    if (erase && this.eras) {
      return this.func.eval(erase);
    } else {
      var func_v = this.func.eval(erase);
      if (!(func_v instanceof Lam)) {
        return new App(this.eras, func_v, this.argm.eval(erase));
      }
      return func_v.body.subst(0, this.argm).eval(erase);
    }
  }

  check(context = new Context([])) {
    var func_t = this.func.check(context);
    var argm_t = this.argm.check(context);
    var func_T = func_t.eval(true);
    var expect = func_T.bind;
    var actual = argm_t.eval(true);
    if (!func_T instanceof All) {
      throw "Non-function application. Context:\n" + context.show();
    }
    if (func_T.eras !== this.eras) {
      throw "Mismatched erasure on " + this.to_string(context) + ".";
    }
    if (!expect.equal(actual)) {
      throw context.show_mismatch(expect, actual, this.to_string(context) + " application");
    }
    return func_t.eval(false).body.subst(0, this.argm);
  }
}

class Var {
  constructor(index) {
    this.index = index;
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

  uses(depth) {
    return depth === this.index ? 1 : 0;
  }

  equal(other) {
    return other instanceof Var && this.index === other.index;
  }

  eval(erase) {
    return new Var(this.index);
  }

  check(context = new Context([])) {
    return context.get_type(this.index);
  }
}

class Dat {
  constructor() {
  }

  to_string(context = new Context([])) {
    return "Data";
  }

  shift(depth, inc) {
    return new Dat();
  }

  subst(depth, val) {
    return new Dat();
  }

  uses(depth) {
    return 0;
  }

  equal(other) {
    return other instanceof Dat;
  }

  eval(erase) {
    return new Dat();
  }

  check(context = new Context([])) {
    return new Typ();
  }
}

class Idt {
  constructor(name, moti, ctrs) {
    this.name = name;
    this.moti = moti;
    this.ctrs = ctrs;
  }

  to_string(context = new Context([])) {
      var text = "($ " + this.name + " : " + this.moti.to_string(context);
      for (var i = 0; i < this.ctrs.length; ++i) {
        var [ctr_name, ctr_moti] = this.ctrs[i];
        text += " | " + ctr_name + " : " + ctr_moti.to_string(context.extend([this.name, this.moti]));
      }
      return text + " ;)";
  }

  shift(depth, inc) {
      var name = this.name;
      var moti = this.moti.shift(depth, inc);
      var ctrs = this.ctrs.map(([ctr_name, ctr_type]) => [ctr_name, ctr_type.shift(depth + 1, inc)]);
      return new Idt(name, moti, ctrs);
  }

  subst(depth, val) {
      var name = this.name;
      var moti = this.moti.subst(depth, val);
      var ctrs = this.ctrs.map(([ctr_name, ctr_type]) => [ctr_name, ctr_type.subst(depth + 1, val.shift(0, 1))]);
      return new Idt(name, moti, ctrs);
  }

  uses(depth) {
      moti = this.moti.uses(depth);
      ctrs = this.ctrs.reduce((sum, [_, ctr_type]) => sum + ctr_type.uses(depth + 1), 0);
      return moti + ctrs;
  }

  equal(other) {
    if (other instanceof Idt) {
      var moti = this.moti.equal(other.moti);
      var strs = this.ctrs.reduce((eq, ctr, i) => eq && ctr.equal(other.ctrs[i]), true);
      return moti && ctrs;
    }
    return false;
  }

  eval(erase) {
      var name = this.name;
      var moti = this.moti.eval(erase);
      var ctrs = this.ctrs.map(([ctr_name, ctr_type]) => [ctr_name, ctr_type.eval(erase)]);
      return new Idt(name, moti, ctrs);
  }

  check(context = new Context([])) {
    return new Dat();
  }

  get_vars() {
    var moti_vars = [];
    var self_moti = this.moti;
    while (self_moti instanceof All) {
      moti_vars.push(self_moti.name);
      self_moti = self_moti.body;
    }
    var ctrs_vars = [];
    for (var [ctr_name, ctr_type] of this.ctrs) {
      var ctr_vars = [];
      while (ctr_type instanceof All) {
        ctr_vars.push(ctr_type.name);
        ctr_type = ctr_type.body;
      }
      ctrs_vars.push([ctr_name, ctr_vars]);
    }
    return [moti_vars, ctrs_vars];
  }

  derive_type() {
    var self = this;
    
    function build_indices(depth, indices_type) {
      if (indices_type instanceof All) {
          var eras = indices_type.eras;
          var name = indices_type.name;
          var bind = indices_type.bind;
          var body = build_indices(depth + 1, indices_type.body);
          return new Lam(eras, name, bind, body);
        } else {
          return build_motive(depth);
        }
      }

      function build_motive(depth) {
        var eras = true;
        var name = self.name;
        var bind = self.moti.shift(0, depth);
        var body = build_constructor(depth + 1, 0);
        return new All(eras, name, bind, body);
      }

      function build_constructor(depth, num) {
        if (num < self.ctrs.length) {
          var [ctr_name, ctr_type] = self.ctrs[num];
          var eras = false;
          var name = ctr_name;
          var bind = ctr_type.shift(1, depth).subst(0, new Var(num));
          var body = build_constructor(depth + 1, num + 1);
          return new All(eras, name, bind, body);
        } else {
          return build_return_type(depth, self.moti, 0, new Var(self.ctrs.length));
        }
      }

      function build_return_type(depth, indices_type, index, return_type) {
        if (indices_type instanceof All) {
          var return_type = new App(indices_type.eras, return_type, new Var(depth - index - 1));
          return build_return_type(depth, indices_type.body, index + 1, return_type);
        } else {
          return return_type;
        }
      }

      return build_indices(0, self.moti);
  }

  derive_constructor(name) {
    var self = this;

    for (var ctr_index = 0; ctr_index < self.ctrs.length; ++ctr_index) {
      var [ctr_name, ctr_type] = self.ctrs[ctr_index];
      if (name === ctr_name) {
        break;
      }
    }

    function build_lambdas(depth, fields_type) {
      if (fields_type instanceof All) {
        var eras = fields_type.eras;
        var name = fields_type.name;
        var bind = fields_type.bind;
        var body = build_lambdas(depth + 1, fields_type.body);
        return new Lam(eras, name, bind, body);
      } else {
        return build_body(depth, ctr_type, 0, new Var(self.ctrs.length - ctr_index - 1));
      }
    }

    function build_body(depth, fields_type, field_index, term) {
      if (fields_type instanceof All) {
        var field = new Var(depth - field_index - 1);
        if (fields_type.bind.uses(field_index) > 0) {
          var field = new App(true, field, new Var(self.ctrs.length));
          for (var i = 0; i < self.ctrs.length; ++i) {
            field = new App(false, field, new Var(self.ctrs.length - i - 1));
          }
        }
        var body = new App(fields_type.eras, term, field);
        return build_body(depth, fields_type.body, field_index + 1, body);
      } else {
        return term;
      }
    }

    return build_lambdas(0, ctr_type.subst(0, self.derive_type()).eval(false));
  }

  to_inductive() {
    var self = this;

    function build_motive(depth, motive_type, self_type) {
      if (motive_type instanceof All) {
        var eras = motive_type.eras;
        var name = motive_type.name;
        var bind = motive_type.bind;
        var body = build_motive(depth + 1, motive_type.body, new App(motive_type.eras, self_type.shift(0, 1), new Var(0)));
        return new All(eras, name, bind, body);
      } else {
        return new All(false, "self", self_type, motive_type);
      }
    }

    function build_constructor(depth, fields_type, self_value) {
      if (fields_type instanceof All) {
        if (fields_type.bind.uses(depth) > 0) {
          var eras_0 = true;
          var name_0 = fields_type.name;
          var bind_0 = fields_type.bind.subst(depth, self.derive_type().shift(0, depth));
          var eras_1 = fields_type.eras;
          var name_1 = "~" + fields_type.name;
          var bind_1 = new App(false, fields_type.bind.shift(0, 1), new Var(0));
          var newfty = fields_type.body.shift(0, 1);
          var newval = new App(fields_type.eras, self_value.shift(0, 2), new Var(1));
          var body_1 = build_constructor(depth + 2, newfty, newval);
          return new All(eras_0, name_0, bind_0, new All(eras_1, name_1, bind_1, body_1));
        } else {
          var eras_0 = fields_type.eras;
          var name_0 = fields_type.name;
          var bind_0 = fields_type.bind;
          var newfty = fields_type.body;
          var newval = new App(fields_type.eras, self_value.shift(0, 1), new Var(0));
          var body_0 = build_constructor(depth + 1, newfty, newval);
          return new All(eras_0, name_0, bind_0, body_0);
        }
      } else {
        return new App(false, fields_type, self_value);
      }
    }

    var ind_name = self.name + "_ind";
    var ind_moti = build_motive(0, self.moti, self.derive_type());
    var ind_ctrs = [];
    for (var [ctr_name, ctr_type] of self.ctrs) {
      var ind_ctr_name = ctr_name;
      var ind_ctr_type = build_constructor(0, ctr_type, self.derive_constructor(ctr_name));
      ind_ctrs.push([ind_ctr_name, ind_ctr_type]);
    }
    return new Idt(ind_name, ind_moti, ind_ctrs).eval(false);
  }
}

class Ity {
  constructor(data) {
    this.data = data;
  }

  to_string(context = new Context([])) {
    return "&" + this.data.to_string(context);
  }

  shift(depth, inc) {
    return new Ity(this.data.shift(depth, inc));
  }

  subst(depth, val) {
    return new Ity(this.data.subst(depth, val));
  }

  uses(depth) {
    return this.data.uses(depth);
  }

  equal(other) {
    return other instanceof Ity && this.data.equal(other.data);
  }

  eval(erase) {
    var data_v = this.data.eval(false);
    if (data_v instanceof Idt) {
      return data_v.derive_type().eval(erase);
    } else {
      return new Ity(data_v);
    }
  }

  check(context = new Context([])) {
    var data_v = this.data.eval(false);
    if (data_v instanceof Idt) {
      return data_v.derive_type().check(context).eval(false);
    } else {
      throw "Couldn't determine datatype statically. Context:\n" + context.show();
    }
  }
}

class Con {
  constructor(data, name) {
    this.data = data;
    this.name = name;
  }

  to_string(context = new Context([])) {
    return "@" + this.data.to_string(context) + "." + this.name;
  }

  shift(depth, inc) {
    var data = this.data.shift(depth, inc);
    var name = this.name;
    return new Con(data, name);
  }

  subst(depth, val) {
    var data = this.data.subst(depth, val);
    var name = this.name;
    return new Con(data, name);
  }

  uses(depth) {
    return this.data.uses(depth);
  }

  equal(other) {
    if (other instanceof Con) {
      var data = this.data.equal(other.data);
      var name = this.name === other.name;
      return data && name;
    }
    return false;
  }

  eval(erase) {
    var data_v = this.data.eval(false);
    if (data_v instanceof Idt) {
      return data_v.derive_constructor(this.name).eval(erase);
    } else {
      return new Con(data_v, this.name);
    }
  }

  check(context = new Context([])) {
    var data_v = this.data.eval(false);
    if (data_v instanceof Idt) {
      return data_v.derive_constructor(this.name).check(context).eval(false);
    } else {
      throw "Couldn't determine datatype statically. Context:\n" + context.show();
    }
  }
}

class Ind {
  constructor(data, term, moti, cses) {
    this.data = data;
    this.term = term;
    this.moti = moti;
    this.cses = cses;
  }

  to_string(context = new Context([])) {
    var vars = this.data.eval(false).to_inductive().get_vars();
    var text = "";
    text += "(?" + this.data.to_string(context);
    text += " " + this.term.to_string(context) + " ->";
    text += " " + this.moti.to_string(vars[0].reduce((ctx, v) => ctx.extend([v, null]), context))
    for (var i = 0; i < vars[1].length; ++i) {
      var [ctr_name, ctr_vars] = vars[1][i];
      text += " | " + ctr_name + " => " + this.cses[i].to_string(ctr_vars.reduce((ctx,v) => ctx.extend([v, null]), context));
    }
    return text + " ;)";
  }

  get_indices(context) {
    function extract(depth, term_type) {
      if (term_type instanceof All) {
        return extract(depth + 1, term_type.body);
      }
      if (term_type instanceof App) {
        return extract(depth, term_type.func).concat([term_type.argm.shift(0, -depth)]);
      }
      return [];
    }
    return extract(0, this.term.check(context));
  }

  build() {
    function build_term(type, body, vars) {
      if (vars > 0) {
        return new Lam(type.eras, type.name, type.bind, build_term(type.body, body, vars - 1));
      } else {
        return body;
      }
    }
    var indu = this.data.eval(false).to_inductive();
    var vars = indu.get_vars();
    var moti = build_term(indu.moti, this.moti, vars[0].length);
    var cses = [];
    for (var ctr_index = 0; ctr_index < indu.ctrs.length; ++ctr_index) {
      var [[ctr_name, ctr_type], ctr_body] = [indu.ctrs[ctr_index], this.cses[ctr_index]];
      var ctr_type = ctr_type.subst(0, moti).eval(false);
      var ctr_term = build_term(ctr_type, ctr_body, vars[1][ctr_index][1].length);
      cses.push([ctr_name, ctr_term, ctr_type]);
    }
    return [moti, cses];
  }

  shift(depth, inc) {
    var vars = this.data.eval(false).to_inductive().get_vars();
    var data = this.data.shift(depth, inc);
    var term = this.term.shift(depth, inc);
    var moti = this.moti.shift(depth + vars[0].length, inc);
    var cses = this.cses.map((cse, i) => cse.shift(depth + vars[1][i].length, inc));
    return new Ind(data, term, moti, cses);
  }

  subst(depth, val) {
    var vars = this.data.eval(false).to_inductive().get_vars();
    var data = this.data.subst(depth, val);
    var term = this.term.subst(depth, val);
    var moti = this.moti.subst(depth + vars[0].length, val);
    var cses = this.cses.map((cse, i) => cse.subst(depth + vars[1][i].length, val));
    return new Ind(data, term, moti, cses);
  }

  uses(depth) {
    var vars = this.data.eval(false).to_inductive().get_vars();
    var data = this.data.uses(depth);
    var term = this.term.uses(depth);
    var moti = this.moti.uses(depth + vars[0].length);
    var cses = this.cses.reduce((sum, cse, i) => sum + cse.uses(depth + vars[1][i].length), 0);
    return data + term + moti + cses;
  }

  equal(other) {
    var data = this.data.equal(other.data);
    var term = this.term.equal(other.term);
    var moti = this.moti.equal(other.moti);
    var cses = this.cses.reduce((eq, ctr, i) => eq && ctr.equal(other.cses[i]), true);
    return data && term && moti && cses;
  }

  eval(erase) {
    if (!erase) {
      var data = this.data.eval(erase);
      var term = this.term.eval(erase);
      var moti = this.moti.eval(erase);
      var cses = this.cses.map((cse) => cse.eval(erase));
      return new Ind(data, term, moti, cses);
    } else {
      var [moti, cses] = this.build();
      var term = new App(true, this.term, moti);
      for (var [cse_name, cse_term, cse_type] of cses) {
        var term = new App(false, term, cse_term);
      }
      return term.eval(erase);
    }
  }

  check(context = new Context([])) {
    // Check term type
    var indices = this.get_indices(context);
    var term_t = this.term.check(context);
    var data_t = this.data.eval(false).derive_type();
    for (var idx of indices) {
      data_t = data_t.body.subst(0, idx);
    }
    var expect = term_t.eval(true);
    var actual = data_t.eval(true);
    if (!expect.equal(actual)) {
      throw context.show_mismatch(expect, actual, "term of " + this.to_string(context));
    }

    // Check case types
    var [moti, cses] = this.build();
    for (var [cse_name, cse_term, cse_type] of cses) {
      var expect = cse_type.eval(true);
      var actual = cse_term.check(context).eval(true);
      if (!expect.equal(actual)) {
        throw context.show_mismatch(expect, actual, "case " + cse_name + " of " + this.to_string(context));
      }
    }

    // Build return type
    var result = moti.eval(false);
    for (var idx of indices) {
      result = result.body.subst(0, idx);
    }
    result = result.body.subst(0, this.term);
    return result;
  }
}

function string_to_term(code) {
  var index = 0;

  function is_space(char) {
    return char === " " || char === "\t" || char === "\n";
  }

  function is_name_char(char) {
    return "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_~".indexOf(char) !== -1;
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

  function parse_term(context, only_data) {
    // Comment
    if (match("--")) {
      while (index < code.length && code[index] !== "\n") {
        index += 1;
      }
      return parse_term(context, false);
    }

    // Application
    else if (match("(")) {
      var func = parse_term(context, false);
      while (index < code.length && !match(")")) {
        var eras = match("-");
        var argm = parse_term(context, false);
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
      var bind = parse_term(context, false);
      var skip = parse_exact("}");
      var body = parse_term(context.extend([name, null]), false);
      return new All(eras, name, bind, body);
    }

    // Lambda
    else if (match("[")) {
      var eras = match("-");
      var name = parse_name();
      var skip = parse_exact(":");
      var bind = parse_term(context, false);
      var skip = parse_exact("]");
      var body = parse_term(context.extend([name, null]), false);
      return new Lam(eras, name, bind, body);
    }

    // Definition
    else if (match("def")) {
      var name = parse_name();
      var term = parse_term(context, false);
      var body = parse_term(context.extend([name, term]), false);
      return body;

    // IDT (inline)
    } else if (match("$") || match("data")) {
      var inli = code[index - 1] === "$";
      var name = parse_name();
      var skip = parse_exact(":");
      var type = parse_term(context, false);
      var ctrs = [];
      while (match("|")) {
        var ctr_name = parse_name();
        var ctr_skip = parse_exact(":");
        var ctr_type = parse_term(context.extend([name, null]), false);
        ctrs.push([ctr_name, ctr_type]);
      }
      parse_exact(";");
      var data = new Idt(name, type, ctrs);
      // Inline declaration
      if (inli) {
        return data

      // Global declaration (creates defs)
      } else {
        var context = context.extend([name.toUpperCase(), data]);
        var context = context.extend([name, data]);
        var context = context.extend([name, new Ity(data)]);
        for (var ctr of ctrs) {
          context = context.extend([ctr[0], new Con(data, ctr[0])]);
        }
        return parse_term(context, false);
      }

    // IDT Type
    } else if (match("&")) {
      var data = parse_term(context, true);
      return new Ity(data);

    // IDT Constructor
    } else if (match("@")) {
      var data = parse_term(context, true);
      var skip = parse_exact(".");
      var name = parse_name();
      return new Con(data, name);

    // IDT Induction
    } else if (match("?")) {
      var data = parse_term(context, true);
      var vars = data.eval(false).to_inductive().get_vars();
      var term = parse_term(context, false);
      var skip = parse_exact("->");
      var moti = parse_term(vars[0].reduce((ctx, v) => ctx.extend([v, null]), context), false);
      var cses = [];
      for (var [ctr_name, ctr_vars] of vars[1]) {
        var skip = parse_exact("|");
        var skip = parse_exact(ctr_name);
        var skip = parse_exact("=>");
        var body = parse_term(ctr_vars.reduce((ctx, v) => ctx.extend([v, null]), context), false);
        cses.push(body);
      }
      var skip = parse_exact(";");
      return new Ind(data, term, moti, cses);

    // Variable (named)
    } else {
      var name = parse_name();
      var skip = 0;
      while (match("'")) {
        skip += 1;
      }
      var bind = context.find_by_name(name, skip, only_data);
      if (bind) {
        return new Nik(name, bind[1]);
      }
      error("Parse error, unbound variable '" + name + "'.\n");
    }
  }

  return parse_term(new Context([]), false);
}

module.exports = string_to_term;
