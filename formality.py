from nasic import *
from list import *

# DECISOES:
# lam sem type
# var com strings porque se nao seria possivel parsear e stringificar
# -> mas ai o to_net precisa do infer...

# ok, fazer o seguinte: vars tem bruijn indices
# -> mas existe um novo termo, Nam, que guarda uma string
# -> dessa forma, parsear eh possivel sem inferencias
# -> na hora de inferir, o Nam simplesmente vira um Var on-the-spot

# eh possivel evitar totalmente reduce, shift, etc., usando interaction nets!
# -> pra isso, eh preciso recuperar tipos totalmente, tal como All e Typ
# -> lambdas precisam guardar o tipo, apps precisam descarta-lo
# -> um modo "erased" pode ser usado, que retorna lambdas com None, quando sabe-se que o tipo nao sera usado
# -> tambem eh preciso recuperar free variables
# -> bruijn indexes nao sao mais necessarios, posso mudar para nomes
# -> implementacao drasticamente simplificada! centenas de linhas de codigo a menos

# double [x : Nat] [y : Nat]
#     case x -> Nat
#     | succ => Nat< succ Nat< succ (fold pred) > >
#     | zero => Nat< zero >

# double (x : Nat) (y : Nat)
#   case x -> Nat
#   | succ => Nat[ <succ <succ <fold pred>>> ]
#   | zero => Nat[ zero ]

# double (x : Nat) (y : Nat) Nat =
#   case x -> Nat
#   | succ => Nat{ succ (succ (fold pred)) }
#   | zero => Nat{ zero }

# induction (n : Nat) (P : (n : Nat) -> Type) (S : (n : Nat) (p : P n) (P (Nat.succ n))) (Z : P Nat.zero) (P n) =
#   case n -> P self
#   | succ => s pred (fold pred P s z)
#   | zero => z

# subst {A : Type} {x : A} {y : A} {e : Eq A x y} {P : {x : A} Type} {px : P x} (P y) = :A :x :y :e
#   case e -> {P : {x : A} Type} {px : P x} || P y
#   | refl => px

class Typ:
    def __init__(self):
        pass

    def to_string(self, scope):
        return "Type"

    def shift(self, enclose, inc):
        return Typ()

    def substitute(self, depth, value):
        return Typ()

    def build_net(self, net, var_ptrs):
        typ_addr = net.alloc_node(3)
        net.link_ports(Pointer(typ_addr, 0), Pointer(typ_addr, 2))
        return Pointer(typ_addr, 1)

    def infer(self, context):
        return Typ()

class All:
    def __init__(self, name, bind, body):
        self.name = name
        if bind == None:
            raise(Exception("wtf"))
        self.bind = bind
        self.body = body

    def to_string(self, scope):
        return "{" + self.name + " : " + self.bind.to_string(scope) + "} " + self.body.to_string(scope.prepend(self.name))

    def shift(self, depth, inc):
        return All(self.name, self.bind.shift(depth, inc), self.body.shift(depth + 1, inc)) 

    def substitute(self, depth, value):
        return All(self.name, self.bind.substitute(depth, value), self.body.substitute(depth + 1, value))

    def build_net(self, net, var_ptrs):
        all_addr = net.alloc_node(2)
        tup_addr = net.alloc_node(2)
        net.link_ports(Pointer(all_addr, 1), Pointer(all_addr, 1))
        net.link_ports(Pointer(all_addr, 0), Pointer(tup_addr, 2))
        bind_ptr = self.bind.build_net(net, var_ptrs)
        net.link_ports(Pointer(tup_addr, 1), bind_ptr)
        body_ptr = self.body.build_net(net, var_ptrs.prepend(Pointer(all_addr, 1)))
        net.link_ports(Pointer(all_addr, 2), body_ptr)
        return Pointer(tup_addr, 0)

    def infer(self, context):
        return Typ()

class Lam: 
    def __init__(self, name, bind, body):
        self.name = name
        self.bind = bind
        self.body = body

    def to_string(self, scope):
        return "[" + self.name + " : " + self.bind.to_string(scope) + "] " + self.body.to_string(scope.prepend(self.name))

    def shift(self, depth, inc):
        return Lam(self.name, self.bind.shift(depth, inc), self.body.shift(depth + 1, inc)) 

    def substitute(self, depth, value):
        return Lam(self.name, self.bind.substitute(depth, value), self.body.substitute(depth + 1, value))

    def build_net(self, net, var_ptrs):
        lam_addr = net.alloc_node(1)
        tup_addr = net.alloc_node(1)
        net.link_ports(Pointer(lam_addr, 1), Pointer(lam_addr, 1))
        net.link_ports(Pointer(lam_addr, 0), Pointer(tup_addr, 2))
        bind_ptr = self.bind.build_net(net, var_ptrs)
        net.link_ports(Pointer(tup_addr, 1), bind_ptr)
        body_ptr = self.body.build_net(net, var_ptrs.prepend(Pointer(lam_addr, 1)))
        net.link_ports(Pointer(lam_addr, 2), body_ptr)
        return Pointer(tup_addr, 0)

    def infer(self, context):
        body = self.body.infer(extend(context, self.name, self.bind.shift(0, 1)))
        return All(self.name, self.bind, body)

class App:
    def __init__(self, func, argm):
        self.func = func
        self.argm = argm

    def to_string(self, scope):
        return "(" + self.func.to_string(scope) + " " + self.argm.to_string(scope) + ")"

    def shift(self, depth, inc):
        return App(self.func.shift(depth, inc), self.argm.shift(depth, inc))

    def substitute(self, depth, value):
        return App(self.func.substitute(depth, value), self.argm.substitute(depth, value))

    def build_net(self, net, var_ptrs):
        app_addr = net.alloc_node(1)
        tup_addr = net.alloc_node(1)
        net.link_ports(Pointer(tup_addr, 2), Pointer(app_addr, 0))
        net.link_ports(Pointer(tup_addr, 1), Pointer(tup_addr, 1))
        func_ptr = self.func.build_net(net, var_ptrs)
        net.link_ports(Pointer(tup_addr, 0), func_ptr)
        argm_ptr = self.argm.build_net(net, var_ptrs)
        net.link_ports(Pointer(app_addr, 1), argm_ptr)
        return Pointer(app_addr, 2)

    def infer(self, context):
        func = self.func.infer(context)
        return func.body.substitute(0, self.argm)

class Var:
    def __init__(self, index):
        self.index = index

    def to_string(self, scope):
        name = scope.get(self.index)
        if name is not None:
            return name
        else:
            return "#" + str(self.index - scope.len())

    def shift(self, depth, inc):
        return Var(self.index if self.index < depth else self.index + inc)

    def substitute(self, depth, value):
        if self.index == depth:
            return value.shift(0, depth)
        elif self.index > depth:
            return Var(self.index - 1)
        else:
            return Var(self.index)

    def build_net(self, net, var_ptrs):
        ptr = var_ptrs.get(self.index)
        if ptr is None:
            var_addr = net.alloc_node(self.index + 1000 - var_ptrs.len())
            net.link_ports(Pointer(var_addr, 0), Pointer(var_addr, 2))
            return Pointer(var_addr, 1)
        else:
            dups_ptr = net.enter_port(ptr)
            if net.enter_port(ptr) == ptr:
                return ptr
            else:
                dup_addr = net.alloc_node(2000 + ptr.addr)
                net.link_ports(Pointer(dup_addr, 0), ptr)
                net.link_ports(Pointer(dup_addr, 1), dups_ptr)
                return Pointer(dup_addr, 2)

    def infer(self, context):
        return context.get(self.index)[1]

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

    def substitute(self, depth, value):
        return Idt(self.name, self.type.substitute(depth, value), map(lambda ctr: ctr.substitute(depth + 1, value), self.ctrs))

    def build_net(self, net, var_ptrs):
        idt_type_addr = net.alloc_node(4)
        idt_bind_addr = net.alloc_node(4)
        idt_type_ptr = self.type.build_net(net, var_ptrs)
        net.link_ports(Pointer(idt_type_addr, 1), idt_type_ptr)
        net.link_ports(Pointer(idt_bind_addr, 1), Pointer(idt_bind_addr, 1))
        net.link_ports(Pointer(idt_bind_addr, 0), Pointer(idt_type_addr, 2))
        ctr_slot_ptr = Pointer(idt_bind_addr, 2)
        for i in xrange(len(self.ctrs)):
            ctr_addr = net.alloc_node(4)
            ctr_type_ptr = self.ctrs[i][1].build_net(net, var_ptrs.prepend(Pointer(idt_bind_addr, 1)))
            net.link_ports(Pointer(ctr_addr, 1), ctr_type_ptr)
            net.link_ports(Pointer(ctr_addr, 0), ctr_slot_ptr)
            ctr_slot_ptr = Pointer(ctr_addr, 2)
        net.link_ports(ctr_slot_ptr, ctr_slot_ptr)
        return Pointer(idt_type_addr, 0)

    def infer(self, context):
        return self.type

def net_to_term(net, ptr, vars, exit):
    label = net.nodes[ptr.addr].label

    # Lam / Var / App
    if label == 1:

        # Lam
        if ptr.port == 0:
            bind = net_to_term(net, net.enter_port(Pointer(ptr.addr, 1)), vars, exit)
            ptr  = net.enter_port(Pointer(ptr.addr, 2))
            vars = vars.prepend(Pointer(ptr.addr, 1))
            body = net_to_term(net, net.enter_port(Pointer(ptr.addr, 2)), vars, exit)
            return Lam("x" + str(vars.len() - 1), bind, body)

        # Var
        if ptr.port == 1:
            return Var(vars.find(lambda p: p == ptr)[0])

        # App
        if ptr.port == 2:
            argm = net_to_term(net, net.enter_port(Pointer(ptr.addr, 1)), vars, exit)
            ptr  = net.enter_port(Pointer(ptr.addr, 0))
            func = net_to_term(net, net.enter_port(Pointer(ptr.addr, 0)), vars, exit)
            return App(func, argm)

    # All / Var
    if label == 2:
        # All
        if ptr.port == 0:
            bind = net_to_term(net, net.enter_port(Pointer(ptr.addr, 1)), vars, exit)
            ptr  = net.enter_port(Pointer(ptr.addr, 2))
            vars = vars.prepend(Pointer(ptr.addr, 1))
            body = net_to_term(net, net.enter_port(Pointer(ptr.addr, 2)), vars, exit)
            return All("x" + str(vars.len() - 1), bind, body)

        # Var
        if ptr.port == 1:
            return Var(vars.find(lambda p: p == ptr)[0])

    # Typ
    if label == 3:
        return Typ()

    # Idt / Var
    if label == 4:
        # Idt
        if ptr.port == 0:
            type = net_to_term(net, net.enter_port(Pointer(ptr.addr, 1)), vars, exit)
            ptr  = net.enter_port(Pointer(ptr.addr, 2))
            vars = vars.prepend(Pointer(ptr.addr, 1))
            ptr  = net.enter_port(Pointer(ptr.addr, 2))
            ctrs = []
            while net.enter_port(ptr) != ptr:
                ctrs.append(("ctr" + str(len(ctrs)), net_to_term(net, net.enter_port(Pointer(ptr.addr, 1)), vars, exit)))
                ptr = net.enter_port(Pointer(ptr.addr, 2))
            return Idt("x" + str(vars.len() - 1), type, ctrs)

        # Var
        if ptr.port == 1:
            return Var(vars.find(lambda p: p == ptr)[0])

    # Var
    if label >= 1000 and label < 2000:
        return Var(label - 1000 + vars.len())

    # Dup
    if label >= 2000:
        if ptr.port == 0:
            return net_to_term(net, net.enter_port(Pointer(ptr.addr, exit.head)), vars, exit.tail)
        else:
            return net_to_term(net, net.enter_port(Pointer(ptr.addr, 0)), vars, exit.prepend(ptr.port))

def extend(context, name, type):
    return context.map(lambda (name, term): (name, term.shift(0, 1))).prepend((name, type))

def term_to_net(term):
    net = Net()
    root_addr = net.alloc_node(0)
    term_ptr = term.build_net(net, List())
    net.link_ports(Pointer(root_addr, 0), Pointer(root_addr, 2)) 
    net.link_ports(Pointer(root_addr, 1), term_ptr)
    return (net, term_ptr)

def evaluate(term):
    (net, _) = term_to_net(term)
    net.evaluate()
    term = net_to_term(net, net.enter_port(Pointer(0, 1)), List(), List()) 
    return term

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
            parsed = []
            while Cursor.index < len(code) and not match(")"):
                parsed.append(parse_term(scope))
                skip_spaces()
            return reduce(App, parsed)

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

        # Variable
        else:
            name = parse_name()
            found = scope.find(lambda n: n == name)
            if not found:
                raise(Exception("Unbound variable: '" + str(name) + "' at index " + str(Cursor.index) + "."))
            return Var(found[0])
    return parse_term(List())

nat  = "{P : Type} {S : {n : P} P} {Z : P} P"
n0   = "[P : Type] [S : {n : P} P] [Z : P] Z"
n1   = "[P : Type] [S : {n : P} P] [Z : P] (S Z)"
n2   = "[P : Type] [S : {n : P} P] [Z : P] (S (S Z))"
n3   = "[P : Type] [S : {n : P} P] [Z : P] (S (S (S Z)))"
add  = "[a : "+nat+"] [b : "+nat+"] [P : Type] [S : {x : P} P] [Z : P] (a P S (b P S Z))"
main = "("+add+" "+n2+" "+n3+")"
main = "data Nat : Type | Succ : {x : Nat} Nat | Zero : Nat"

term = string_to_term(main)

(net, ptr) = term_to_net(term)

print "Input term:"
print term.to_string(List())
print ""

print "Recovered form net:"
print net_to_term(net, net.enter_port(Pointer(0, 1)), List(), List()).to_string(List())
print ""

net.reduce()

print "Reduced:"
print net_to_term(net, net.enter_port(Pointer(0, 1)), List(), List()).to_string(List())
print ""

print "Inferred type:"
print term.infer(List()).to_string(List())
print ""
