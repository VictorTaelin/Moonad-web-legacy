from nasic import *
from list import *

class Context:
    def __init__(self, list = List()):
        self.list = list

    def shift(self, depth, inc):
        return Context(self.list.map(lambda (name, type, value): (name, type.shift(depth, inc), value.shift(depth, inc))))

    def extend(self, (name, type, value)):
        return Context(self.list.prepend((name, type, value)))

    def view(self):
        for i in xrange(self.list.len()):
            (name, type, value) = self.list.get(i)
            print name + " : " + type.to_string(self.to_scope()) + " = " + value.to_string(self.to_scope())

    def get(self, index):
        return self.list.get(index)

    def to_scope(self):
        return self.list.map(lambda (name, type, value): name)

class Typ:
    def __init__(self):
        pass

    def to_string(self, scope):
        return "Type"

    def shift(self, enclose, inc):
        return Typ()

    def equal(self, other):
        return isinstance(other, Typ)

    def infer(self, context):
        return Typ()

    def refine(self, context):
        return Typ()

class All:
    def __init__(self, name, bind, body):
        self.name = name
        self.bind = bind
        self.body = body

    def to_string(self, scope):
        return "{" + self.name + " : " + self.bind.to_string(scope) + "} " + self.body.to_string(scope.prepend(self.name))

    def shift(self, depth, inc):
        return All(self.name, self.bind.shift(depth, inc), self.body.shift(depth + 1, inc)) 

    def equal(self, other):
        return isinstance(other, All) and self.bind.equal(other.bind) and self.body.equal(other.body)

    def infer(self, context):
        bind_t = self.bind.infer(context)
        body_t = self.body.infer(context.shift(0, 1).extend((self.name, self.bind.shift(0, 1), Var(0))))
        if not bind_t.equal(Typ()) or not body_t.equal(Typ()):
            raise(Exception("Forall not a type."))
        return Typ()

    def refine(self, context):
        bind_v = self.bind.refine(context)
        body_v = self.body.refine(context.shift(0, 1).extend((self.name, self.bind.shift(0, 1), Var(0))))
        return All(self.name, bind_v, body_v)

class Lam: 
    def __init__(self, name, bind, body):
        self.name = name
        self.bind = bind
        self.body = body

    def to_string(self, scope):
        return "[" + self.name + " : " + self.bind.to_string(scope) + "] " + self.body.to_string(scope.prepend(self.name))

    def shift(self, depth, inc):
        return Lam(self.name, self.bind.shift(depth, inc), self.body.shift(depth + 1, inc)) 

    def equal(self, other):
        return isinstance(other, Lam) and self.bind.equal(other.bind) and self.body.equal(other.body)

    def infer(self, context):
        bind_v = self.bind.refine(context)
        body_t = self.body.infer(context.shift(0, 1).extend((self.name, self.bind.shift(0, 1), Var(0))))
        result = All(self.name, bind_v, body_t)
        result.infer(context).equal(Typ())
        return result

    def refine(self, context):
        bind_v = self.bind.refine(context)
        body_v = self.body.refine(context.shift(0, 1).extend((self.name, self.bind.shift(0, 1), Var(0))))
        return Lam(self.name, bind_v, body_v)

class App:
    def __init__(self, func, argm):
        self.func = func
        self.argm = argm

    def to_string(self, scope):
        return "(" + self.func.to_string(scope) + " " + self.argm.to_string(scope) + ")" 

    def shift(self, depth, inc):
        return App(self.func.shift(depth, inc), self.argm.shift(depth, inc))

    def equal(self, other):
        return isinstance(other, App) and self.func.equal(other.func) and self.argm.equal(other.argm)

    def infer(self, context):
        func_t = self.func.infer(context)
        argm_v = self.argm.refine(context)
        argm_t = self.argm.infer(context)
        if not isinstance(func_t, All):
            raise(Exception("Non-function application."))
        elif not func_t.bind.refine(context).equal(argm_t.refine(context)):
            print self.func.to_string(context.to_scope()) + " applied to " + self.argm.to_string(context.to_scope()) + ":"
            print "- " + func_t.bind.refine(context).to_string(context.to_scope())
            print "- " + argm_t.refine(context).to_string(context.to_scope())
            raise(Exception("Type mismatch."))
        else:
            return func_t.body.refine(context.extend((func_t.name, func_t.bind, argm_v)))

    def refine(self, context):
        func_v = self.func.refine(context)
        argm_v = self.argm.refine(context)
        if isinstance(func_v, Lam):
            return func_v.body.refine(context.extend((func_v.name, func_v.bind, argm_v)))
        else:
            return App(func_v, argm_v)

class Var:
    def __init__(self, index):
        self.index = index

    def to_string(self, scope):
        name = scope.get(self.index)
        if name is not None:
            return name# + "#" + str(self.index)
        else:
            return "#" + str(self.index)

    def shift(self, depth, inc):
        return Var(self.index if self.index < depth else self.index + inc)

    def equal(self, other):
        return isinstance(other, Var) and self.index == other.index

    def infer(self, context):
        return context.get(self.index)[1]

    def refine(self, context):
        return context.get(self.index)[2]

class Idt:
    def __init__(self, name, type, ctrs):
        self.name = name
        self.type = type
        self.ctrs = ctrs

    def to_string(self, scope):
        result = "data " + self.name + " : " + self.type.to_string(scope) + " "
        for (name, type) in self.ctrs:
            result += "| " + name + " : " + type.to_string(scope.prepend(self.name)) + " "
        return result

    def shift(self, depth, inc):
        return Idt(self.name, self.type.shift(depth, inc), map(lambda ctr: ctr.shift(depth + 1, inc), self.ctrs))

    def equal(self, other):
        return isinstance(other, Idt) and self.type.equal(other.type) and all([a[1].equal(b[1]) for (a,b) in zip(self.ctrs, other.ctrs)])

    def infer(self, context):
        return self.type

    def refine(self, context):
        type = self.type.refine(context)
        ctrs = map(lambda (name, type): (name, type.refine(context.extend((self.name, self.type, Var(0))))), self.ctrs)
        return Idt(self.name, type, ctrs) 

class Ctr:
    def __init__(type, name, vals):
        self.type = type
        self.name = name
        self.vals = vals

    def to_string(self, scope):
        return "@" + self.type.to_string(scope) + " " + self.name + " " + " ".join(map(lambda val: val.to_string(scope)), self.vals)

    def shift(self, depth, inc):
        return Ctr(self.type.shift(depth, inc), self.name, map(lambda val: val.shift(depth, inc), self.vals))

    def equal(self, other):
        return isinstance(other, Ctr) and self.type.equal(other.type) and all([a.equal(b) for (a,b) in zip(self.vals, other.vals)])

    def refine(self, context):
        return Ctr(self.type.refine(context), self.name, map(lambda val: val.refine(context), self.vals))

def string_to_term(code):
    class Cursor:
        index = 0

    def is_space(char):
        return char == ' ' or char == '\t'

    def is_name_char(char):
        return (  char >= b'a' and char <= b'z'
               or char >= b'A' and char <= b'Z'
               or char >= b'0' and char <= b'9'
               or char == b'_'
               or char == b'-')

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
        
    def parse_term(scope):
        # Application
        if match("("):
            func = parse_term(scope)
            while Cursor.index < len(code) and not match(")"):
                argm = parse_term(scope)
                func = App(func, argm)
                skip_spaces()
            return func

        # Forall
        elif match("{"):
            name = parse_name()
            skip = parse_exact(":")
            bind = parse_term(scope)
            skip = parse_exact("}")
            body = parse_term(scope.prepend(name))
            return All(name, bind, body)

        # Lambda
        elif match("["):
            name = parse_name()
            skip = parse_exact(":")
            bind = parse_term(scope)
            skip = parse_exact("]")
            body = parse_term(scope.prepend(name))
            return Lam(name, bind, body)

        # Type
        elif match("Type"):
            return Typ()

        # IDT
        elif match("data"):
            name = parse_name()
            skip = parse_exact(":")
            type = parse_term(scope)
            ctrs = []
            while match("|"):
                ctr_name = parse_name()
                ctr_skip = parse_exact(":")
                ctr_type = parse_term(scope.prepend(name))
                ctrs.append((ctr_name, ctr_type))
            return Idt(name, type, ctrs)

        # Constructor
        #elif match("@"):
            #name = parse_name()
            #skip = parse_exact(":")
            #type = parse_term(scope)
            #ctrs = []
            #while match("|"):
                #ctr_name = parse_name()
                #ctr_skip = parse_exact(":")
                #ctr_type = parse_term(scope.prepend(name))
                #ctrs.append((ctr_name, ctr_type))
            #return Idt(name, type, ctrs)

        # Variable (Bruijn indexed)
        elif match("#"):
            index = parse_name()
            return Var(int(index))

        # Variable (named)
        else:
            name = parse_name()
            found = scope.find(lambda n: n == name)
            if not found:
                raise(Exception("Unbound variable: '" + str(name) + "' at index " + str(Cursor.index) + "."))
            return Var(found[0])

    return parse_term(List())

nat   = "{P : Type} {S : {n : P} P} {Z : P} P"
n0    = "[P : Type] [S : {n : P} P] [Z : P] Z"
n1    = "[P : Type] [S : {n : P} P] [Z : P] (S Z)"
n2    = "[P : Type] [S : {n : P} P] [Z : P] (S (S Z))"
n3    = "[P : Type] [S : {n : P} P] [Z : P] (S (S (S Z)))"
add   = "[a : "+nat+"] [b : "+nat+"] [P : Type] [S : {x : P} P] [Z : P] (a P S (b P S Z))"
mul   = "[a : "+nat+"] [b : "+nat+"] [P : Type] [S : {x : P} P] (a P (b P S))"

cbool = "{P : Type} {T : P} {F : P} P"
ctrue = "[P : Type] [T : P] [F : P] T"
cfals = "[P : Type] [T : P] [F : P] F"

main  = "("+mul+" "+n3+" "+n3+")"

main  = "data Bool : Type | true : Bool | false : Bool"

term = string_to_term(main)

print "Input term:"
print term.to_string(List())
print ""

print "Normal form:"
print term.refine(Context()).to_string(List())
print ""

print "Inferred type:"
print term.infer(Context()).to_string(List())
print ""



