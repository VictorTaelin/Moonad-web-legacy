import cProfile

class Context:
    def __init__(self, list = []):
        self.list = list

    def shift(self, depth, inc):
        new_list = []
        for binder in self.list:
            if binder is None:
                new_list.append(None)
            else:
                new_list.append((binder[0], binder[1].shift(depth, inc), binder[2].shift(depth, inc)))
        return Context(new_list)

    def extend(self, binder):
        return Context([binder] + self.shift(0, 1).list)

    def get(self, index):
        return self.list[index] if index < len(self.list) else None

    def find(self, name):
        for i in xrange(len(self.list)):
            if self.list[i][0] == name:
                return self.list[i]
        return None

def string_to_term(code):
    class Cursor:
        index = 0

    def is_space(char):
        return char in " \t\n"

    def is_name_char(char):
        return char in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_"

    def skip_spaces():
        while Cursor.index < len(code) and is_space(code[Cursor.index]):
            Cursor.index += 1
        return Cursor.index

    def match(string):
        skip_spaces()
        sliced = code[Cursor.index : Cursor.index + len(string)]
        if sliced == string:
            Cursor.index += len(string)
            return sliced
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
        
    def parse_term(context):
        # Comment
        if match("--"):
            while Cursor.index < len(code) and code[Cursor.index] != "\n":
                Cursor.index += 1
            return parse_term(context)

        # Application
        elif match("("):
            func = parse_term(context)
            while Cursor.index < len(code) and not match(")"):
                eras = match("-")
                argm = parse_term(context)
                func = App(eras, func, argm)
                skip_spaces()
            return func

        # Forall
        elif match("{"):
            eras = match("-")
            name = parse_name()
            skip = parse_exact(":")
            bind = parse_term(context.extend((name, Var(0), Var(0))))
            skip = parse_exact("}")
            body = parse_term(context.extend((name, Var(0), Var(0))))
            return All(eras, name, bind, body)

        # Lambda
        elif match("["):
            eras = match("-")
            name = parse_name()
            skip = parse_exact(":")
            bind = parse_term(context.extend((name, Var(0), Var(0))))
            skip = parse_exact("]")
            body = parse_term(context.extend((name, Var(0), Var(0))))
            return Lam(eras, name, bind, body)

        # Dep
        elif match("@"):
            name = parse_name()
            body = parse_term(context.extend((name, Var(0), Var(0))))
            return Dep(name, body)

        # New
        elif match("#"):
            type = parse_term(context)
            term = parse_term(context)
            return New(type, term)

        # Era
        elif match("."):
            term = parse_term(context)
            return Era(term)

        # Use
        elif match("~"):
            term = parse_term(context)
            return Use(term)

        # Pro
        elif match("^"):
            type = parse_term(context)
            term = parse_term(context)
            return Pro(type, term)

        # Type
        elif match("Type"):
            return Typ()

        # Definition
        elif match("def"):
            name = parse_name()
            term = parse_term(context)
            body = parse_term(context.extend((name, Var(0), term)))
            return body

        # Variable (Bruijn indexed)
        elif match("#"):
            index = parse_name()
            return Var(int(index))

        # Variable (named)
        else:
            name = parse_name()
            bind = context.find(name)
            if bind:
                return bind[2]
            raise(Exception("Unbound variable: '" + str(name) + "' at index " + str(Cursor.index) + "-"))

    return parse_term(Context())

class Typ:
    def __init__(self):
        pass

    def to_string(self, context):
        return "Type"

    def shift(self, depth, inc):
        return Typ()

    def equal(self, other, context):
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

    def equal(self, other, context):
        return isinstance(other, All) and self.bind.equal(other.bind, context) and self.body.equal(other.body, context)

    def check(self, context):
        ex_ctx = context.extend((self.name, self.bind, Var(0)))
        bind_t = self.bind.check(ex_ctx)
        body_t = self.body.check(ex_ctx)
        if not bind_t.equal(Typ(), context) or not body_t.equal(Typ(), context):
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

    def equal(self, other, context):
        return isinstance(other, Lam) and self.bind.equal(other.bind, context) and self.body.equal(other.body, context)

    def check(self, context):
        ex_ctx = context.extend((self.name, self.bind, Var(0)))
        bind_v = self.bind.eval(ex_ctx)
        body_t = self.body.check(ex_ctx).eval(ex_ctx)
        result = All(self.eras, self.name, bind_v, body_t)
        result.check(context).equal(Typ(), context)
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

    def equal(self, other, context):
        return isinstance(other, App) and self.func.equal(other.func, context) and self.argm.equal(other.argm, context)

    def check(self, context):
        func_t = self.func.check(context)
        argm_v = self.argm.eval(context)
        argm_t = self.argm.check(context)
        if not isinstance(func_t, All):
            raise(Exception("Non-function application."))
        ex_ctx = context.extend((func_t.name, func_t.bind, argm_v.shift(0, 1)))
        expect = func_t.bind.eval(ex_ctx).shift(0, -1)
        actual = argm_t.eval(context)
        if not expect.equal(actual, context):
            raise(Exception("Type mismatch on '" + self.to_string(context) + "' application.\n"
                + "- Expected : " + expect.to_string(Context()) + "\n"
                + "- Actual   : " + actual.to_string(Context())))
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
            return binder[0]
        else:
            return "#" + str(self.index)

    def shift(self, depth, inc):
        return Var(self.index if self.index < depth else self.index + inc)

    def equal(self, other, context):
        return isinstance(other, Var) and self.index == other.index

    def check(self, context):
        return context.get(self.index)[1].eval(context)

    def eval(self, context):
        return context.get(self.index)[2]

    def erase(self, context):
        if context.get(self.index) is None:
            return Era(Var(self.index))
        else:
            return context.get(self.index)[2]

# Erased term
class Era:
    def __init__(self, term):
        self.term = term

    def to_string(self, context):
        return "." + self.term.to_string(context)

    def shift(self, depth, inc):
        return Era(self.term.shift(depth, inc))

    def equal(self, other, context):
        return isinstance(other, Era) and self.term.equal(other.term, context)

    def check(self, context):
        # ctx |- t : A
        # ------------------
        # ctx |- E(t) : E(A)
        return self.term.check(context).erase(Context())

    def eval(self, context):
        return self.term.eval(context).erase(Context())

    def erase(self, context):
        return self.term.erase(context)

# The type of a self-dependent intersection
class Dep: 
    def __init__(self, name, body):
        self.name = name
        self.body = body

    def to_string(self, context):
        return "@" + self.name + self.body.to_string(context.extend((self.name, self.erase(Context()).shift(0, 1), Var(0))))

    def shift(self, depth, inc):
        return Dep(self.name, self.body.shift(depth + 1, inc)) 

    def equal(self, other, context):
        return isinstance(other, Dep) and self.body.equal(other.body, context)

    def check(self, context):
        # ctx |- E(A) : *     ctx, x : E(A) |- B : *
        # ------------------------------------------
        # ctx |- @x.A : *
        # TODO
        return Typ()

    def eval(self, context):
        return Dep(self.name, self.body.eval(context.extend((self.name, self.erase(Context()).shift(0, 1), Var(0)))))

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

    def equal(self, other, context):
        return isinstance(other, New) and self.type.equal(other.type, context) and self.term.equal(other.term, context)

    def check(self, context):
        # ctx |- E(t) : E(A)     ctx |- t : [E(t)/x]A     ctx |- @x. A : *
        # ----------------------------------------------------------------
        # ctx |- #x.A t : @x.A
        type_v = self.type.eval(context)
        eras_v = self.term.erase(Context())
        eras_t = eras_v.check(context)
        eras_T = type_v.erase(Context())
        term_t = self.term.check(context)
        term_T = type_v.body.eval(context.extend((type_v.name, eras_t, eras_v)))
        if not eras_t.equal(eras_T, context) or not term_t.equal(term_T, context):
            raise(Exception("Type mismatch."))
        return type_v

    def eval(self, context):
        return New(self.type.eval(context), self.term.eval(context))

    def erase(self, context):
        return self.term.erase(context)

# Extracts term from self-dependent intersection
class Use:
    def __init__(self, term):
        self.term = term

    def to_string(self, context):
        return "~" + self.term.to_string(context)

    def shift(self, depth, inc):
        return Use(self.term.shift(depth, inc))

    def equal(self, other, context):
        return isinstance(other, Use) and self.term.equal(other.term, context)

    def check(self, context):
        # ctx |- t : @x.A
        # ----------------------------
        # ctx |- ~t : [E(t)/x]A
        term_t = self.term.check(context)
        if not isinstance(term_t, Dep):
            raise(Exception("Can't use non-Dep."))
        subs_v = self.term.eval(context).erase(Context())
        subs_t = term_t.erase(Context())
        ex_ctx = context.extend((term_t.name, subs_t.shift(0, 1), subs_v.shift(0, 1)))
        return term_t.body.eval(ex_ctx).shift(0, -1).eval(context)

    def eval(self, context):
        term_v = self.term.eval(context)
        if not isinstance(term_v, New):
            return Use(term_v)
        subs_v = self.term.eval(context).erase(Context())
        subs_t = term_v.type.erase(context)
        ex_ctx = context.extend((term_v.type.name, subs_t.shift(0, 1), subs_v.shift(0, 1)))
        return term_v.term.eval(ex_ctx).shift(0, -1)

    def erase(self, context):
        return self.term.erase(context)

class Pro:
    def __init__(self, type, term):
        self.type = type
        self.term = term

    def to_string(self, context):
        return "^" + self.type.to_string(context) + " " + self.term.to_string(context)

    def shift(self, depth, inc):
        return Pro(self.type.shift(depth, inc), self.term.shift(depth, inc))

    def equal(self, other, context):
        return self.term.erase(Context()).equal(other.erase(Context()), context)

    def check(self, context):
        # ctx |- t : E(A)     ctx |- @x.A : *
        # -----------------------------------
        # ctx |- ^x.A t : @x.A
        actual = self.term.check(context)
        expect = self.type.erase(Context())
        if not expect.equal(actual, context):
            raise(Exception("Type mismatch on promotion."))
        return self.type

    def eval(self, context):
        type_v = self.type.eval(context)
        term_v = self.term.eval(context)
        if not isinstance(term_v, Era):
            return Pro(type_v, term_v)
        return term_v.term

    def erase(self, context):
        return self.term

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

    def test [P : {-b : CBool} Type] [T : (P -CTrue)] [F : (P -CFals)] T

    -- Bool as a self-dependent intersection of an annotated CBool with its erasure
    def Bool @self {P : {-b : CBool} Type} {T : (P -CTrue)} {F : (P -CFals)} (P -self)
    def True #Bool [P : {-b : CBool} Type] [T : (P -CTrue)] [F : (P -CFals)] T
    def Fals #Bool [P : {-b : CBool} Type] [T : (P -CTrue)] [F : (P -CFals)] F

    -- Induction principle on Bool
    def Elim {b : Bool} {P : {x : Bool} Type} {T : (P True)} {F : (P Fals)} (P b)
    def elim [b : Bool] [P : {x : Bool} Type] [T : (P True)] [F : (P Fals)] (~b [-x : CBool](P (^Bool x)) T F)

    -- Church Nat
    def CNat            {P : Type} {S : {x : P} P} {Z : P} P
    def CSuc [n : CNat] [P : Type] [S : {x : P} P] [Z : P] (S (n P S Z))
    def CZer            [P : Type] [S : {x : P} P] [Z : P] Z

    -- def Nat            [n : CNat]    {P : {-b : CNat} Type} {S : {-n : CNat} {p : (P -n)} (P -(CSuc n))} {Z : (P -CZer)} (P -n)
    -- def Suc [i : CNat] [n : (Nat i)] [P : {-b : CNat} Type] [S : {-n : CNat} {p : (P -n)} (P -(CSuc n))] [Z : (P -CZer)] (S -i (n P S Z))
    -- def Zer                          [P : {-b : CNat} Type] [S : {-n : CNat} {p : (P -n)} (P -(CSuc n))] [Z : (P -CZer)] Z
    -- def ind [i : CNat] [n : (Nat i)] [P : {-b : CNat} Type] [S : {-n : CNat} {p : (P -n)} (P -(CSuc n))] [Z : (P -CZer)] (n P S Z)

    -- Nat as a self-dependent intersection of an annotated CNat with its erasure
    def Nat           @self {P : {-b : CNat} Type} {S : {-n : CNat} {p : (P -n)} (P -(CSuc n))} {Z : (P -CZer)} (P -self)
    def Suc [n : Nat]  #Nat [P : {-b : CNat} Type] [S : {-n : CNat} {p : (P -n)} (P -(CSuc n))] [Z : (P -CZer)] (S -.n (~n P S Z))
    def Zer            #Nat [P : {-b : CNat} Type] [S : {-n : CNat} {p : (P -n)} (P -(CSuc n))] [Z : (P -CZer)] Z

    def induction [n : CNat] [P : {x : CNat} Type] [S : {-n : CNat} {p : (P n)} (P (CSuc n))] [Z : (P CZer)] (~^Nat n P S Z)

    induction

{n : {P : Type} {S : {x : P} P} {Z : P} P}
{P : {x : {P : Type} {S : {x : P} P} {Z : P} P} Type}
{S : {-n : {P : Type} {S : {x : P} P} {Z : P} P} {p : (P n)} (P [P : Type] [S : {x : P} P] [Z : P] (S (((n P) S) Z)))}
{Z : (P [P : Type] [S : {x : P} P] [Z : P] Z)}
(P -n)


    -- Induction principle on Nat
    def Induction {n : Nat} {P : {x : Nat} Type} {S : {-n : Nat} {p : (P n)} (P (Suc n))} {Z : (P Zer)} (P n)
    def induction [n : Nat] [P : {x : Nat} Type] [S : {-n : Nat} {p : (P n)} (P (Suc n))] [Z : (P Zer)] (~n [-x : CNat](P (^Nat x)) [-n : CNat][p : (P ^Nat n)](S -^Nat n p) Z)


    f : {P : {n : CNat} Type}
        {S : {n : CNat} [p : (P n)] (P (CSuc n))}
        {Z : (P CZer)}
        {n : CNat}
        (P n)
    f = [P : {-n : CNat} Type]
        [S : {-n : CNat} [p : (P -n)] (P -(CSuc n))]
        [Z : (P -CZer)]
        [n : CNat]
        (n P S Z)


    induction

    -- Checks it
    (the Induction induction)
"""

def foo():
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

foo()
#cProfile.run('foo()')
