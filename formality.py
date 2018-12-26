class Context:
    def __init__(self, list = []):
        self.list = list

    def shift(self, depth, inc):
        return Context(map(lambda (name, type, value): (name, type.shift(depth, inc), value.shift(depth, inc)), self.list))

    def extend(self, (name, type, term)):
        shifted = lambda term: term.shift(0, 1) if term is not None else Var(0)
        return Context([(name, shifted(type), shifted(term))] + self.shift(0, 1).list)

    def get(self, index):
        return self.list[index] if index < len(self.list) else None

    def find(self, name):
        skip = 0
        while name[-1] == "'":
            name = name[:-1]
            skip += 1
        for i in xrange(len(self.list)):
            if self.list[i][0] == name:
                if skip > 0:
                    skip -= 1
                else:
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

class Typ:
    def __init__(self):
        pass

    def to_string(self, context):
        return "Type"

    def shift(self, depth, inc):
        return Typ()

    def equal(self, other):
        return isinstance(other, Typ)

    def get_call_expr(self):
        return (self, [])

    def get_binders(self):
        return []

    def check(self, context):
        return Typ()

    def eval(self, context):
        return Typ()

class All:
    def __init__(self, name, bind, body):
        self.name = name
        self.bind = bind
        self.body = body

    def to_string(self, context):
        return "{" + self.name + " : " + self.bind.to_string(context) + "} " + self.body.to_string(context.extend((self.name, self.bind, None)))

    def shift(self, depth, inc):
        return All(self.name, self.bind.shift(depth, inc), self.body.shift(depth + 1, inc)) 

    def subst(self, depth, val):
        return All(self.name, self.bind.subst(depth, inc), self.body.subst(depth + 1, inc))

    def equal(self, other):
        return isinstance(other, All) and self.bind.equal(other.bind) and self.body.equal(other.body)

    def get_call_expr(self):
        return (self, [])

    def get_binders(self):
        return [(self.name, self.bind)] + self.body.get_binders()

    def check(self, context):
        bind_t = self.bind.check(context)
        body_t = self.body.check(context.extend((self.name, self.bind, None)))
        if not bind_t.equal(Typ()) or not body_t.equal(Typ()):
            raise(Exception("Forall not a type."))
        return Typ()

    def eval(self, context):
        bind_v = self.bind.eval(context)
        body_v = self.body.eval(context.extend((self.name, self.bind, None)))
        return All(self.name, bind_v, body_v)

class Lam: 
    def __init__(self, name, bind, body):
        self.name = name
        self.bind = bind
        self.body = body

    def to_string(self, context):
        return "[" + self.name + " : " + self.bind.to_string(context) + "] " + self.body.to_string(context.extend((self.name, self.bind, None)))

    def shift(self, depth, inc):
        return Lam(self.name, self.bind.shift(depth, inc), self.body.shift(depth + 1, inc)) 

    def equal(self, other):
        return isinstance(other, Lam) and self.bind.equal(other.bind) and self.body.equal(other.body)

    def get_call_expr(self):
        return (self, [])

    def get_binders(self):
        return [(self.name, self.bind)] + self.body.get_binders()

    def check(self, context):
        bind_v = self.bind.eval(context)
        body_t = self.body.check(context.extend((self.name, self.bind, None)))
        result = All(self.name, bind_v, body_t)
        result.check(context).equal(Typ())
        return result.eval(context)

    def eval(self, context):
        bind_v = self.bind.eval(context)
        body_v = self.body.eval(context.extend((self.name, self.bind, None)))
        return Lam(self.name, bind_v, body_v)

class App:
    def __init__(self, func, argm):
        self.func = func
        self.argm = argm

    def to_string(self, context):
        (func, argms) = self.get_call_expr()
        result = "(" + func.to_string(context)
        for argm in argms:
            result += " " + argm.to_string(context)
        return result + ")"

    def shift(self, depth, inc):
        return App(self.func.shift(depth, inc), self.argm.shift(depth, inc))

    def equal(self, other):
        return isinstance(other, App) and self.func.equal(other.func) and self.argm.equal(other.argm)

    def get_call_expr(self):
        (func, argms) = self.func.get_call_expr()
        return (func, argms + [self.argm])

    def get_binders(self):
        return []

    def check(self, context):
        func_t = self.func.check(context)
        argm_v = self.argm.eval(context)
        argm_t = self.argm.check(context)
        if not isinstance(func_t, All):
            raise(Exception("Non-function application."))
        elif not func_t.bind.eval(context).equal(argm_t.eval(context)):
            raise(Exception("Type mismatch on '" + self.to_string(context) + "' application.\n"
                + "- Expected : " + func_t.bind.eval(context).to_string(context) + "\n"
                + "- Actual   : " + argm_t.eval(context).to_string(context)))
        else:
            return func_t.body.eval(context.extend((func_t.name, func_t.bind, argm_v)).shift(0, -1))

    def eval(self, context):
        func_v = self.func.eval(context)
        argm_v = self.argm.eval(context)
        if isinstance(func_v, Lam):
            return func_v.body.eval(context.extend((func_v.name, func_v.bind, argm_v)).shift(0, -1))
        else:
            return App(func_v, argm_v)

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

    def get_call_expr(self):
        return (self, [])

    def get_binders(self):
        return []

    def check(self, context):
        return context.get(self.index)[1].eval(context)

    def eval(self, context):
        return context.get(self.index)[2]

class Idt:
    def __init__(self, name, type, ctrs):
        self.name = name # string
        self.type = type # term
        self.ctrs = ctrs # [(string, term)]

    def to_string(self, context):
        result = "<" + self.name + " : " + self.type.to_string(context)
        for (i, (name, type)) in enumerate(self.ctrs):
            result += " | " + name + " : " + type.to_string(context.extend((self.name, self.type, Var(0))))
        return result + ">"

    def shift(self, depth, inc):
        return Idt(self.name, self.type.shift(depth, inc), [(name, type.shift(depth + 1, inc)) for (name, type) in self.ctrs])

    def equal(self, other):
        return isinstance(other, Idt) and self.type.equal(other.type) and all([a[1].equal(b[1]) for (a,b) in zip(self.ctrs, other.ctrs)])

    def get_call_expr(self):
        return (self, [])

    def get_binders(self):
        return []

    def get_ctr_type(self, context, name):
        for (ctr_name, ctr_type) in self.ctrs:
            if ctr_name == name:
                return ctr_type.eval(context.extend((self.name, self.type, self)).shift(0, -1))

    def check(self, context):
        return self.type.eval(context)

    def eval(self, context):
        type = self.type.eval(context)
        ctrs = map(lambda (name, type): (name, type.eval(context.extend((self.name, self.type, None)))), self.ctrs)
        return Idt(self.name, type, ctrs) 

class Ctr:
    def __init__(self, type, name):
        self.type = type
        self.name = name

    def to_string(self, context):
        return "@" + self.type.to_string(context) + "." + self.name

    def shift(self, depth, inc):
        return Ctr(self.type.shift(depth, inc), self.name)

    def equal(self, other):
        return isinstance(other, Ctr) and self.type.equal(other.type) and self.name == other.name

    def get_call_expr(self):
        return (self, [])

    def get_binders(self):
        return []

    def eval(self, context):
        return Ctr(self.type.eval(context), self.name)

    def check(self, context):
        return self.type.eval(context).get_ctr_type(context, self.name)

class Mat:
    def __init__(self, term, moti, cses):
        self.term = term # term
        self.moti = moti # term
        self.cses = cses # [(string, term)]

    @staticmethod
    def extend_motive_context(context, term):
        term_t = term.check(context)
        (datatype, indices) = term_t.get_call_expr()
        for (i, ((name, type), value)) in enumerate(zip(datatype.type.get_binders(), indices)):
            context = context.extend((name, type, value.shift(0, i)))
        context = context.extend(("self", term_t.shift(0, len(indices)), term.shift(0, len(indices))))
        return context

    @staticmethod
    def extend_case_context(context, term, case_name):
        term_t = term.check(context)
        datatype = term.check(context).get_call_expr()[0]
        case_type = datatype.get_ctr_type(context, case_name)
        for (field_name, field_type) in case_type.get_binders():
            context = context.extend((field_name, field_type, None))
        return context

    def to_string(self, context):
        result = "$ " + self.term.to_string(context) + " -> " + self.moti.to_string(Mat.extend_motive_context(context, self.term))
        for (i, (case_name, case_body)) in enumerate(self.cses):
            result += " | " + case_name + " => " + case_body.to_string(Mat.extend_case_context(context, self.term, case_name))
        return result+" ;"

    def shift(self, depth, inc):
        datatype = term.check(context).get_call_expr()[0]
        term = self.term.shift(depth, inc)
        moti = self.moti.shift(depth, inc)
        cses = [(name, body.shift(depth + len(get_ctr_type(context, case_name).get_binders()), inc)) for (name, body) in self.cses]
        return Mat(term, moti, cses)

    def equal(self, other):
        if isinstance(other, Mat):
            term_e = self.term.equal(other.term)
            moti_e = self.moti.equal(other.moti)
            cses_e = all([a[1].equal(b[1]) for (a,b) in zip(self.cses, other.cses)])
            return term_e and moti_e and cses_e
        return False

    def eval(self, context):
        term = self.term.eval(context)
        moti = self.moti.eval(Mat.extend_motive_context(context, self.term))
        cses = [(name, case.eval(Mat.extend_case_context(context, self.term, name))) for (name, case) in self.cses]
        (func, argms) = term.eval(context).get_call_expr()
        if isinstance(func, Ctr):
            for (name, body) in self.cses:
                if name == func.name:
                    new_context = context
                    for (i, argm) in enumerate(argms):
                        new_context = new_context.extend((None, None, argm.shift(0, len(argms) - i - 1)))
                    return body.eval(new_context)
        return Mat(term, moti, cses)

    def check(self, context):
        term_t = self.term.check(context)
        (datatype, index_values) = term_t.get_call_expr()
        motive_depth = len(index_values) + 1

        for (case_name, case_body) in self.cses:
            case_context = Mat.extend_case_context(context, self.term, case_name)
            case_ctr_type = datatype.get_ctr_type(context, case_name)
            case_field_count = len(case_ctr_type.get_binders())

            witness = Ctr(datatype.shift(0, case_field_count), case_name)
            for i in xrange(case_field_count):
                witness = App(witness, Var(case_field_count - i - 1))

            case_expect_type = self.moti.shift(0, case_field_count).eval(Mat.extend_motive_context(case_context, witness)).shift(0, -motive_depth)
            case_actual_type = case_body.check(case_context)

            if not case_actual_type.equal(case_expect_type):
                raise(Exception("Type mismatch on '" + case_name + "' case.\n"
                    + "- Expected : " + case_expect_type.to_string(case_context) + "\n"
                    + "- Actual   : " + case_actual_type.to_string(case_context)))

        return self.moti.eval(Mat.extend_motive_context(context, self.term)).shift(0, -motive_depth)

    def get_call_expr(self):
        return []

    def get_binders(self):
        return []

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
        # IDT
        if match("<"):
            name = parse_name()
            skip = parse_exact(":")
            type = parse_term(context, defs)
            ctrs = []
            while match("|"):
                ctr_name = parse_name()
                ctr_skip = parse_exact(":")
                ctr_type = parse_term(context.extend((name, type, None)), defs)
                ctrs.append((ctr_name, ctr_type))
            parse_exact(">")
            return Idt(name, type, ctrs)

        # Application
        elif match("("):
            func = parse_term(context, defs)
            while Cursor.index < len(code) and not match(")"):
                argm = parse_term(context, defs)
                func = App(func, argm)
                skip_spaces()
            return func

        # Forall
        elif match("{"):
            name = parse_name()
            skip = parse_exact(":")
            bind = parse_term(context, defs)
            skip = parse_exact("}")
            body = parse_term(context.extend((name, bind, None)), defs)
            return All(name, bind, body)

        # Lambda
        elif match("["):
            name = parse_name()
            skip = parse_exact(":")
            bind = parse_term(context, defs)
            skip = parse_exact("]")
            body = parse_term(context.extend((name, bind, None)), defs)
            return Lam(name, bind, body)

        # Type
        elif match("Type"):
            return Typ()

        # Constructor
        elif match("@"):
            type = parse_term(context, defs)
            skip = parse_exact(".")
            name = parse_name()
            return Ctr(type, name)

        # Pattern-match
        elif match("$"):
            term = parse_term(context, defs)
            skip = parse_exact("->")
            moti = parse_term(Mat.extend_motive_context(context, term), defs)
            cses = [] 
            while match("|"):
                cse_name = parse_name()
                cse_skip = parse_exact("=>")
                cse_body = parse_term(Mat.extend_case_context(context, term, cse_name), defs)
                cses.append((cse_name, cse_body))
            parse_exact(";")
            return Mat(term, moti, cses)

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

test = """
    def CNat
        {P : Type} {S : {n : P} P} {Z : P} P

    def c0 [P : Type] [S : {n : P} P] [Z : P]
        Z

    def c1 [P : Type] [S : {n : P} P] [Z : P]
        (S Z)

    def c2 [P : Type] [S : {n : P} P] [Z : P]
        (S (S Z))

    def c3 [P : Type] [S : {n : P} P] [Z : P]
        (S (S (S Z)))

    def add [a : CNat] [b : CNat] [P : Type] [S : {x : P} P] [Z : P]
        (a P S (b P S Z))

    def mul [a : CNat] [b : CNat] [P : Type] [S : {x : P} P]
        (a P (b P S))

    def Nat
        < Nat  : Type
        | succ : {pred : Nat} Nat
        | zero : Nat >

    def succ
        @Nat.succ

    def zero
        @Nat.zero

    def pred [n : Nat]
        $ n    -> Nat
        | succ => pred
        | zero => zero ;

    def Bool
        < Bool  : Type
        | true  : Bool
        | false : Bool >

    def true
        @Bool.true

    def false
        @Bool.false
    
    def bool-elim [b : Bool] [P : {x : Bool} Type] [T : (P @Bool.true)] [F : (P @Bool.false)]
        $ b     -> (P self)
        | true  => T
        | false => F ;

    def Pair [A : Type] [B : Type]
        < Pair : Type
        | new  : {a : A} {b : B} Pair >

    def fst [A : Type] [B : Type] [pair : (Pair A B)]
        $ pair -> A
        | new  => a ;

    def snd [A : Type] [B : Type] [pair : (Pair A B)]
        $ pair -> B
        | new  => b ;

    def test-mul (mul c3 c3)
    def test-pair (@(Pair Bool Nat).new true @Nat.zero)
    def test-fst (fst Bool Nat test-pair)
    def test-snd (snd Bool Nat test-pair)
    def test-pred (pred (@Nat.succ (@Nat.succ (@Nat.succ @Nat.zero))))
    def test-elim bool-elim

    test-pair
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
