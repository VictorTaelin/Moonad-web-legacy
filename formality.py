# coding=utf-8

class Context:
    def __init__(self, list = []):
        self.list = list

    def shift(self, depth, inc):
        new_list = []
        for binder in self.list:
            if binder is None:
                new_list.append(None)
            else:
                nam = binder[0]
                typ = binder[1].shift(depth, inc)
                val = binder[2].shift(depth, inc)
                new_list.append((nam, typ, val))
        return Context(new_list)

    def extend(self, binder):
        return Context([binder] + self.shift(0, 1).list)

    def get(self, index):
        return self.list[index] if index < len(self.list) else None

    def find(self, name):
        for i in xrange(len(self.list)):
            if self.list[i][0] == name:
                return (i, self.list[i])
        return None

    def len(self):
        return len(self.list)

class Defs:
    def __init__(self, dict = {}):
        self.dict = dict

    def define(self, key, val):
        dict = self.dict.copy()
        dict[key] = val
        return Defs(dict)

    def get(self, key):
        return self.dict[key] if key in self.dict else None

def string_to_term(code):
    class Cursor:
        index = 0

    def is_space(char):
        return char == ' ' or char == '\t' or char == '\n'

    def is_name_char(char):
        return (  char >= 'a' and char <= 'z'
               or char >= 'A' and char <= 'Z'
               or char >= '0' and char <= '9'
               or char == "'"
               or char == '_'
               or char == '-')

    def skip_spaces():
        while Cursor.index < len(code) and is_space(code[Cursor.index]):
            Cursor.index += 1
        return Cursor.index

    def match(string):
        skip_spaces()
        if Cursor.index < len(code):
            matched = code[Cursor.index : Cursor.index + len(string)] == string
            if matched:
                Cursor.index += len(string)
            return matched
        return False

    def parse_exact(string):
        if not match(string):
            raise(Exception("Parse error, expected '" + str(string) + "' at index " + str(Cursor.index) + "."))
        
    def parse_name():
        skip_spaces()
        name = ""
        while Cursor.index < len(code) and is_name_char(code[Cursor.index]):
            name = name + code[Cursor.index]
            Cursor.index += 1
        return name
        
    def parse_term(context, defs):
        # Application
        if match("("):
            func = parse_term(context, defs)
            while Cursor.index < len(code) and not match(")"):
                eras = match("-")
                argm = parse_term(context, defs)
                func = App(eras, func, argm)
                skip_spaces()
            return func

        # Forall
        elif match("{"):
            eras = match("-")
            name = parse_name()
            skip = parse_exact(":")
            bind = parse_term(context.extend((name, Var(0), Var(0))), defs)
            skip = parse_exact("}")
            body = parse_term(context.extend((name, Var(0), Var(0))), defs)
            return All(eras, name, bind, body)

        # Lambda
        elif match("["):
            eras = match("-")
            name = parse_name()
            skip = parse_exact(":")
            bind = parse_term(context.extend((name, Var(0), Var(0))), defs)
            skip = parse_exact("]")
            body = parse_term(context.extend((name, Var(0), Var(0))), defs)
            return Lam(eras, name, bind, body)

        # Dep
        elif match("@"):
            name = parse_name()
            body = parse_term(context.extend((name, Var(0), Var(0))), defs)
            return Dep(name, body)

        # New
        elif match("#"):
            type = parse_term(context, defs)
            term = parse_term(context, defs)
            return New(type, term)

        # Era
        elif match("."):
            term = parse_term(context, defs)
            return Era(term)

        # Use
        elif match("~"):
            term = parse_term(context, defs)
            return Use(term)

        # Type
        elif match("Type"):
            return Typ()

        # Definition
        elif match("def"):
            name = parse_name()
            term = parse_term(context, defs)
            body = parse_term(context, defs.define(name, term))
            return body

        # Variable (Bruijn indexed)
        elif match("#"):
            index = parse_name()
            return Var(int(index))

        # Comment
        elif match("--"):
            while Cursor.index < len(code) and not match(")"):
                Cursor.index += 1
            return parse_term(context, defs)

        # Variable (named)
        else:
            name = parse_name()
            var = context.find(name)
            if var:
                return Var(var[0])
            term = defs.get(name)
            if term:
                return term
            raise(Exception("Unbound variable: '" + str(name) + "' at index " + str(Cursor.index) + "."))

    return parse_term(Context(), Defs())

class Typ:
    def __init__(self):
        pass

    def to_string(self, context):
        return "Type"

    def shift(self, depth, inc):
        return Typ()

    def equal(self, other):
        return isinstance(other, Typ)

    def check(self, context):
        return Typ()

    def eval(self, context):
        return Typ()

    def erase(self, context):
        return Typ()

class All:
    def __init__(self, eras, name, bind, body):
        self.eras = eras
        self.name = name
        self.bind = bind
        self.body = body

    def to_string(self, context):
        ex_ctx = context.extend((self.name, self.bind, Var(0)))
        return "{" + ("-" if self.eras else "") + self.name + " : " + self.bind.to_string(ex_ctx) + "} " + self.body.to_string(ex_ctx)

    def shift(self, depth, inc):
        return All(self.eras, self.name, self.bind.shift(depth + 1, inc), self.body.shift(depth + 1, inc)) 

    def equal(self, other):
        return isinstance(other, All) and self.bind.equal(other.bind) and self.body.equal(other.body)

    def check(self, context):
        #print "check all " + self.to_string(context)
        ex_ctx = context.extend((self.name, self.bind, Var(0)))
        bind_t = self.bind.check(ex_ctx)
        body_t = self.body.check(ex_ctx)
        if not bind_t.equal(Typ()) or not body_t.equal(Typ()):
            raise(Exception("Forall not a type."))
        return Typ()

    def eval(self, context):
        ex_ctx = context.extend((self.name, self.bind, Var(0)))
        bind_v = self.bind.eval(ex_ctx)
        body_v = self.body.eval(ex_ctx)
        return All(self.eras, self.name, bind_v, body_v)

    def erase(self, context):
        if self.eras:
            return self.body.erase(context.extend(None)).shift(0, -1)
        else:
            ex_ctx = context.extend((self.name, self.bind, Var(0)))
            bind_e = self.bind.erase(ex_ctx)
            body_e = self.body.erase(ex_ctx)
            return All(self.eras, self.name, bind_e, body_e)

class Lam: 
    def __init__(self, eras, name, bind, body):
        self.eras = eras
        self.name = name
        self.bind = bind
        self.body = body

    def to_string(self, context):
        ex_ctx = context.extend((self.name, self.bind, Var(0)))
        return "[" + ("-" if self.eras else "") + self.name + " : " + self.bind.to_string(ex_ctx) + "] " + self.body.to_string(ex_ctx)

    def shift(self, depth, inc):
        return Lam(self.eras, self.name, self.bind.shift(depth + 1, inc), self.body.shift(depth + 1, inc)) 

    def equal(self, other):
        return isinstance(other, Lam) and self.bind.equal(other.bind) and self.body.equal(other.body)

    def check(self, context):
        #print "check lam " + self.to_string(context)
        ex_ctx = context.extend((self.name, self.bind, Var(0)))
        bind_v = self.bind.eval(ex_ctx)
        body_t = self.body.check(ex_ctx).eval(ex_ctx)
        result = All(self.eras, self.name, bind_v, body_t)
        #result.check(context).equal(Typ())
        return result

    def eval(self, context):
        ex_ctx = context.extend((self.name, self.bind, Var(0)))
        bind_v = self.bind.eval(ex_ctx)
        body_v = self.body.eval(ex_ctx)
        return Lam(self.eras, self.name, bind_v, body_v)

    def erase(self, context):
        if self.eras:
            return self.body.erase(context.extend(None)).shift(0, -1)
        else:
            ex_ctx = context.extend((self.name, self.bind, Var(0)))
            bind_e = self.bind.erase(ex_ctx)
            body_e = self.body.erase(ex_ctx)
            return Lam(self.eras, self.name, bind_e, body_e)

class App:
    def __init__(self, eras, func, argm):
        self.eras = eras
        self.func = func
        self.argm = argm

    def to_string(self, context):
        return "(" + self.func.to_string(context) + " " + ("-" if self.eras else "") + self.argm.to_string(context) + ")"

    def shift(self, depth, inc):
        return App(self.eras, self.func.shift(depth, inc), self.argm.shift(depth, inc))

    def equal(self, other):
        return isinstance(other, App) and self.func.equal(other.func) and self.argm.equal(other.argm)

    def check(self, context):
        #print "check app " + self.to_string(context)
        func_t = self.func.check(context)
        argm_v = self.argm.eval(context)
        argm_t = self.argm.check(context)
        if not isinstance(func_t, All):
            #print "func_v: " + self.func.to_string(context)
            #print "func_t: " + func_t.to_string(context)
            #print "func_t: " + func_t.erase(context).to_string(context)
            #print "argm_v: " + argm_v.to_string(context)
            #print "argm_t: " + argm_t.to_string(context)
            raise(Exception("Non-function application."))
        ex_ctx = context.extend((func_t.name, func_t.bind, argm_v.shift(0, 1)))
        expect = func_t.bind.eval(ex_ctx).shift(0, -1)
        actual = argm_t.eval(context)
        #if not actual.equal(expect) and not actual.erase(context).equal(expect):
        if not actual.equal(expect):
        #if not actual.equal(expect):
            raise(Exception("Type mismatch on '" + self.to_string(context) + "' application.\n"
                + "- Expected : " + expect.to_string(context) + "\n"
                + "- Actual   : " + actual.to_string(context)))
        return func_t.body.eval(ex_ctx).shift(0, -1)

    def eval(self, context):
        func_v = self.func.eval(context)
        argm_v = self.argm.eval(context)
        if not isinstance(func_v, Lam):
            return App(self.eras, func_v, argm_v)
        ex_ctx = context.extend((func_v.name, func_v.bind, argm_v.shift(0, 1)))
        return func_v.body.eval(ex_ctx).shift(0, -1)

    def erase(self, context):
        if self.eras:
            return self.func.erase(context)
        else:
            return App(self.eras, self.func.erase(context), self.argm.erase(context))

class Var:
    def __init__(self, index):
        self.index = index

    def to_string(self, context):
        binder = context.get(self.index)
        if binder is not None:
            name = binder[0]
            for i in xrange(self.index):
                if filter(lambda c: c != "'", context.list[i][0]) == binder[0]:
                    name += "'"
            return name
        else:
            return "#" + str(self.index)

    def shift(self, depth, inc):
        return Var(self.index if self.index < depth else self.index + inc)

    def equal(self, other):
        return isinstance(other, Var) and self.index == other.index

    def check(self, context):
        return context.get(self.index)[1].eval(context)

    def eval(self, context):
        return context.get(self.index)[2]

    def erase(self, context):
        if context.get(self.index) is None:
            raise(Exception("Use of erased variable."))
        else:
            return context.get(self.index)[2]

# The type of a self-dependent intersection
class Dep: 
    def __init__(self, name, body):
        self.name = name
        self.body = body

    def to_string(self, context):
        return "@" + self.name + self.body.to_string(context.extend((self.name, self.erase(context).shift(0, 1), Var(0))))

    def shift(self, depth, inc):
        return Dep(self.name, self.body.shift(depth + 1, inc)) 

    def equal(self, other):
        return isinstance(other, Dep) and self.body.equal(other.body)

    def check(self, context):
        # ctx |- E(A) : *     ctx, x : E(A) |- B : *
        # ------------------------------------------
        # ctx |- @x.A : *
        # TODO
        return Typ()

    def eval(self, context):
        return Dep(self.name, self.body.eval(context.extend((self.name, self.erase(context).shift(0, 1), Var(0)))))

    def erase(self, context):
        return self.body.erase(context.extend(None)).shift(0, -1)

# Instantiates a value of a self-dependent intersection
class New: 
    def __init__(self, type, term):
        self.type = type
        self.term = term

    def to_string(self, context):
        return "#" + self.type.to_string(context) + self.term.to_string(context)

    def shift(self, depth, inc):
        return New(self.type.shift(depth, inc), self.term.shift(depth, inc)) 

    def equal(self, other):
        return isinstance(other, New) and self.type.equal(other.type) and self.term.equal(other.term)

    def check(self, context):
        # ctx |- E(t) : E(A)     ctx |- t : [E(t)/x]A     ctx |- @x. A : *
        # ----------------------------------------------------------------
        # ctx |- #x.A t : @x.A
        type_v = self.type.eval(context)
        eras_v = self.term.erase(context)
        eras_t = eras_v.check(context)
        eras_T = type_v.erase(context)
        term_t = self.term.check(context)
        term_T = type_v.body.eval(context.extend((type_v.name, eras_t, eras_v)))
        if not eras_t.equal(eras_T) or not term_t.equal(term_T):
            raise(Exception("Type mismatch."))
        return type_v

    def eval(self, context):
        return New(self.type.eval(context), self.term.eval(context))

    def erase(self, context):
        return self.term.erase(context)

# Erased view of a self-dependent intersection
class Era:
    def __init__(self, term):
        self.term = term

    def to_string(self, context):
        return "." + self.term.to_string(context)

    def shift(self, depth, inc):
        return Era(self.term.shift(depth, inc))

    def equal(self, other):
        return isinstance(other, Era) and self.term.equal(other.term)

    def check(self, context):
        # ctx |- t : @x.A
        # ----------------------------
        # ctx |- .t : erase(A)
        term_t = self.term.check(context)
        if not isinstance(term_t, Dep):
            raise(Exception("Can't era non-Dep."))
        return term_t.erase(context)

    def eval(self, context):
        term_v = self.term.eval(context)
        if not isinstance(term_v, New):
            return Era(term_v)
        return term_v.erase(context)

    def erase(self, context):
        return self.term.erase(context)

# Annotated view of a self-dependent intersection
class Use:
    def __init__(self, term):
        self.term = term

    def to_string(self, context):
        return "~" + self.term.to_string(context)

    def shift(self, depth, inc):
        return Use(self.term.shift(depth, inc))

    def equal(self, other):
        return isinstance(other, Use) and self.term.equal(other.term)

    def check(self, context):
        # ctx |- t : @x.A
        # ----------------------------
        # ctx |- ~t : [.t/x]A
        term_t = self.term.check(context)
        if not isinstance(term_t, Dep):
            raise(Exception("Can't use non-Dep."))
        subs_v = Era(self.term.eval(context))
        subs_t = term_t.erase(context)
        ex_ctx = context.extend((term_t.name, subs_t.shift(0, 1), subs_v.shift(0, 1)))
        ex_ctx = context.extend((term_t.name, subs_t.shift(0, 1), subs_v.shift(0, 1)))
        return term_t.body.eval(ex_ctx).shift(0, -1).eval(context)

    def eval(self, context):
        term_v = self.term.eval(context)
        if not isinstance(term_v, New):
            return Use(term_v)
        subs_v = Era(self.term.eval(context))
        subs_t = term_v.type.erase(context)
        ex_ctx = context.extend((term_v.type.name, subs_t.shift(0, 1), subs_v.shift(0, 1)))
        return term_v.term.eval(ex_ctx).shift(0, -1)

    def erase(self, context):
        return self.term.erase(context)

test = """
    def CNat          {P : Type} {S : {n : P} P} {Z : P} P
    def c0            [P : Type] [S : {n : P} P] [Z : P] Z
    def cS [n : CNat] [P : Type] [S : {n : P} P] [Z : P] (S (n P S Z))

    def c1 [P : Type] [S : {n : P} P] [Z : P] (S Z)
    def c2 [P : Type] [S : {n : P} P] [Z : P] (S (S Z))
    def c3 [P : Type] [S : {n : P} P] [Z : P] (S (S (S Z)))

    def add [a : CNat] [b : CNat] [P : Type] [S : {x : P} P] [Z : P] (a P S (b P S Z))
    def mul [a : CNat] [b : CNat] [P : Type] [S : {x : P} P] [Z : P] (a P (b P S) Z)

    def the [P : Type] [x : P] x

    -- Church boolean
    def CBool {P : Type} {T : P} {F : P} P
    def CTrue [P : Type] [T : P] [F : P] T
    def CFals [P : Type] [T : P] [F : P] F

    -- Bool as a self-dependent intersection of an annotated CBool with its erasure
    def Bool @self {P : {-b : CBool} Type} {T : (P -CTrue)} {F : (P -CFals)} (P -self)
    def True #Bool [P : {-b : CBool} Type] [T : (P -CTrue)] [F : (P -CFals)] T
    def Fals #Bool [P : {-b : CBool} Type] [T : (P -CTrue)] [F : (P -CFals)] F

    -- Elimination principle for Bool, except it returns (P (.b Bool True Fals))
    -- But (.b Bool True Fals == b). Can we prove that?
    def Elim {b : Bool} {P : {x : Bool} Type} {T : (P True)} {F : (P Fals)} (P (.b Bool True Fals))
    def elim [b : Bool] [P : {x : Bool} Type] [T : (P True)] [F : (P Fals)] (~b [-x : CBool](P (x Bool True Fals)) T F)

    -- Checks that our `elim` is correct.
    (the Elim elim)
"""

term = string_to_term(test)

print "Input term:"
print term.to_string(Context())
print ""

print "Normal form:"
print term.eval(Context()).to_string(Context())
print ""

print "Inferred type:"
print term.check(Context()).to_string(Context())
print ""
