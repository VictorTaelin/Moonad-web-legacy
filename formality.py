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
            print name + " : " + type.to_string(self) + " = " + value.to_string(self)

    def get(self, index):
        return self.list.get(index)

    def to_scope(self):
        return self.list.map(lambda (name, type, value): name)

    def find(self, func):
        return self.list.find(func)

class Typ:
    def __init__(self):
        pass

    def to_string(self, context):
        return "Type"

    def shift(self, enclose, inc):
        return Typ()

    def equal(self, other):
        return isinstance(other, Typ)

    def infer(self, context):
        return Typ()

    def refine(self, context):
        return Typ()

    def get_binders():
        return []

class All:
    def __init__(self, name, bind, body):
        self.name = name
        self.bind = bind
        self.body = body

    def to_string(self, context):
        return "{" + self.name + " : " + self.bind.to_string(context) + "} " + self.body.to_string(context.extend((self.name, self.bind, Var(0))))

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

    def get_binders(self):
        return [(self.name, self.bind)] + self.body.get_binders()

class Lam: 
    def __init__(self, name, bind, body):
        self.name = name
        self.bind = bind
        self.body = body

    def to_string(self, context):
        return "[" + self.name + " : " + self.bind.to_string(context) + "] " + self.body.to_string(context.prepend((self.name, self.bind, Var(0))))

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

    def get_binders():
        return [(self.name, self.bind)] + self.body.get_binders()

class App:
    def __init__(self, func, argm):
        self.func = func
        self.argm = argm

    def to_string(self, context):
        return "(" + self.func.to_string(context) + " " + self.argm.to_string(context) + ")" 

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
            print self.func.to_string(context) + " applied to " + self.argm.to_string(context) + ":"
            print "- " + func_t.bind.refine(context).to_string(context)
            print "- " + argm_t.refine(context).to_string(context)
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

    def get_binders():
        return []

class Var:
    def __init__(self, index):
        self.index = index

    def to_string(self, context):
        name = context.get(self.index)[0]
        if name is not None:
            return name + # "#" + str(self.index)
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

    def get_binders(self):
        return []

class Idt:
    def __init__(self, name, type, ctrs):
        self.name = name # string
        self.type = type # term
        self.ctrs = ctrs # [(string, term)]

    def to_string(self, context):
        return self.name
        #result = "$ " + self.name + " : " + self.type.to_string(context)
        #for (i, (name, type)) in enumerate(self.ctrs):
            #result += " | " + name + " : " + type.to_string(context.extend((self.name, self.type, Var(0))))
        #return result

    def shift(self, depth, inc):
        return Idt(self.name, self.type.shift(depth, inc), [(name, type.shift(depth + 1, inc)) for (name, type) in self.ctrs])

    def equal(self, other):
        return isinstance(other, Idt) and self.type.equal(other.type) and all([a[1].equal(b[1]) for (a,b) in zip(self.ctrs, other.ctrs)])

    def infer(self, context):
        return self.type

    def refine(self, context):
        type = self.type.refine(context)
        ctrs = map(lambda (name, type): (name, type.refine(context.extend((self.name, self.type, Var(0))))), self.ctrs)
        return Idt(self.name, type, ctrs) 

    def get_binders(self):
        return []

    def get_ctr_type(self, context, name):
        for (ctr_name, ctr_type) in self.ctrs:
            if ctr_name == name:
                return ctr_type.refine(context.extend((self.name, self.type, self)))

    def get_cse_context(self, context, name):
        cse_type = self.get_ctr_type(context, name)
        for (field_name, field_type) in cse_type.get_binders():
            context = context.shift(1, 0).extend((field_name, field_type.shift(1, 0), Var(0)))
        return context

class Ctr:
    def __init__(self, type, name):
        self.type = type
        self.name = name

    def to_string(self, context):
        return "@" + self.type.to_string(context) + " " + self.name

    def shift(self, depth, inc):
        return Ctr(self.type.shift(depth, inc), self.name)

    def equal(self, other):
        return isinstance(other, Ctr) and self.type.equal(other.type)

    def refine(self, context):
        return Ctr(self.type.refine(context), self.name)

    def infer(self, context):
        return self.type.get_ctr_type(context, self.name)

    def get_binders(self):
        return []

class Mat:
    def __init__(self, term, moti, cses):
        self.term = term # term
        self.moti = moti # term
        self.cses = cses # [(string, term)]

    def to_string(self, context):
        term_t = self.term.infer(context)
        result = "% " + self.term.to_string(context) + " -> " + self.moti.to_string(context)
        for (i, (cse_name, cse_body)) in enumerate(self.cses):
            body_s = cse_body.to_string(term_t.get_cse_context(context, cse_name))
            result += " | " + cse_name + " => " + body_s
        return result

    def shift(self, depth, inc):
        pass

    def equal(self, other):
        if isinstance(other, Mat):
            term_e = self.term.equal(other.term)
            moti_e = self.moti.equal(other.moti)
            cses_e = all([a[1].equal(b[1]) for (a,b) in zip(self.cses, other.cses)])
            return term_e and moti_e and cses_e
        return False

    def refine(self, context):
        pass

    def infer(self, context):
        pass

    def get_binders(self):
        return []

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
        
    def parse_term(context):
        # IDT
        if match("$"):
            name = parse_name()
            skip = parse_exact(":")
            type = parse_term(context)
            ctrs = []
            while match("|"):
                ctr_name = parse_name()
                ctr_skip = parse_exact(":")
                ctr_type = parse_term(context.extend((name, type, Var(0))))
                ctrs.append((ctr_name, ctr_type))
            return Idt(name, type, ctrs)

        # Application
        elif match("("):
            func = parse_term(context)
            while Cursor.index < len(code) and not match(")"):
                argm = parse_term(context)
                func = App(func, argm)
                skip_spaces()
            return func

        # Forall
        elif match("{"):
            name = parse_name()
            skip = parse_exact(":")
            bind = parse_term(context)
            skip = parse_exact("}")
            body = parse_term(context.extend((name, bind, Var(0))))
            return All(name, bind, body)

        # Lambda
        elif match("["):
            name = parse_name()
            skip = parse_exact(":")
            bind = parse_term(context)
            skip = parse_exact("]")
            body = parse_term(context.extend((name, bind, Var(0))))
            return Lam(name, bind, body)

        # Type
        elif match("Type"):
            return Typ()

        # Constructor
        elif match("@"):
            type = parse_term(context)
            name = parse_name()
            return Ctr(type, name)

        # Pattern-match
        elif match("%"):
            term = parse_term(context)
            skip = parse_exact("->")
            moti = parse_term(context)
            cses = [] 
            ttyp = term.infer(context)
            print "aaaaaaa"
            if not isinstance(ttyp, Idt):
                raise(Exception("Matched value " + term.to_string(context) + " is not a datatype."))
            while match("|"):
                cse_name = parse_name()
                cse_skip = parse_exact("=>")
                context.view()
                cse_body = parse_term(ttyp.get_cse_context(context, cse_name))
                context.view()
                cses.append((cse_name, cse_body))
            return Mat(term, moti, cses)

        # Variable (Bruijn indexed)
        elif match("#"):
            index = parse_name()
            return Var(int(index))

        # Variable (named)
        else:
            name = parse_name()
            found = context.find(lambda (n,t,v): n == name)
            if not found:
                raise(Exception("Unbound variable: '" + str(name) + "' at index " + str(Cursor.index) + "."))
            return Var(found[0])

    return parse_term(Context())

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

Nat   = "$ Nat : Type | succ : {x : Nat} Nat | zero : Nat"
Bool  = "$ Bool : Type | true : Bool | fals : Bool"
Pair  = "$ Pair : Type | new : {a : "+Bool+"} {b : "+Bool+"} Pair"
new   = "@"+Pair+" new"
true  = "@"+Bool+" true"
tt    = "("+new+" "+true+" "+true+")"
main  = "% "+tt+" -> Type | new => b"

term = string_to_term(main)

print "Input term:"
print term.to_string(Context())
print ""

#print "Normal form:"
#print term.refine(Context()).to_string(Context())
#print ""

#print "Inferred type:"
#print term.infer(Context()).to_string(Context())
#print ""
