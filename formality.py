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
        Typ()

    def build_net(self, net, var_ptrs):
        typ_addr = net.alloc_node(3)
        net.link_ports(Pointer(typ_addr, 0), Pointer(typ_addr, 2))
        return Pointer(typ_addr, 1)

    def infer(self, context):
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

    def substitute(self, depth, value):
        return All(self.name, self.bind.substitute(self, depth, value), self.body.substitute(self, depth + 1, value))

    def build_net(self, net, var_ptrs):
        all_addr = net.alloc_node(2)
        bind_ptr = self.bind.build_net(net, var_ptrs)
        net.link_ports(Pointer(all_addr, 1), bind_ptr)
        body_ptr = Lam(self.name, self.bind, self.body).build_net(net, var_ptrs)
        net.link_ports(Pointer(all_addr, 2), body_ptr)
        return Pointer(all_addr, 0)

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
        return Lam(self.name, self.bind.substitute(self, depth, value), self.body.substitute(self, depth + 1, value))

    # TODO cant do this because missing names, can't know what variable binds to what lambda
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
        else:
            return Var(self.index - 1)

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

def net_to_term(net, ptr, var_ptrs, dup_exit):
    label = net.nodes[ptr.addr].label

    # Lam / Var / App
    if label == 1:

        # Lam
        if ptr.port == 0:
            bind = net_to_term(net, net.enter_port(Pointer(ptr.addr, 1)), var_ptrs, dup_exit)
            ptr  = net.enter_port(Pointer(ptr.addr, 2))
            body = net_to_term(net, net.enter_port(Pointer(ptr.addr, 2)), var_ptrs.prepend(Pointer(ptr.addr, 1)), dup_exit)
            return Lam("x" + str(var_ptrs.len()), bind, body)

        # Var
        if ptr.port == 1:
            (index, _) = var_ptrs.find(lambda p: p == ptr)
            return Var(index)

        # App
        if ptr.port == 2:
            argm = net_to_term(net, net.enter_port(Pointer(ptr.addr, 1)), var_ptrs, dup_exit)
            ptr  = net.enter_port(Pointer(ptr.addr, 0))
            func = net_to_term(net, net.enter_port(Pointer(ptr.addr, 0)), var_ptrs, dup_exit)
            return App(func, argm)

    # All
    if label == 2:
        type = net_to_term(net, net.enter_port(Pointer(ptr.addr, 1)), var_ptrs, dup_exit)
        body = net_to_term(net, net.enter_port(Pointer(ptr.addr, 2)), var_ptrs, dup_exit).body
        return All("x" + str(var_ptrs.len()), type, body)

    # Typ
    if label == 3:
        return Typ()

    # Var
    if label >= 1000 and label < 2000:
        return Var(label - 1000 + var_ptrs.len())

    # Dup
    if label >= 2000:
        if ptr.port == 0:
            return net_to_term(net, net.enter_port(Pointer(ptr.addr, dup_exit.head)), var_ptrs, dup_exit.tail)
        else:
            return net_to_term(net, net.enter_port(Pointer(ptr.addr, 0)), var_ptrs, dup_exit.prepend(ptr.port))

def extend(context, name, type):
    return context.map(lambda (name, term): (name, term.shift(0, 1))).prepend((name, type))

def term_to_net(term):
    net = Net()
    root_addr = net.alloc_node(0)
    term_ptr = term.build_net(net, List())
    net.link_ports(Pointer(root_addr, 0), Pointer(root_addr, 2)) 
    net.link_ports(Pointer(root_addr, 1), term_ptr)
    return (net, term_ptr)

def reduce(term):
    (net, _) = term_to_net(term)
    net.reduce()
    term = net_to_term(net, net.enter_port(Pointer(0, 1)), List(), List()) 
    return term

ID = Lam("P", Typ(), Lam("x", Var(0), Var(0)))

NAT = All("P", Typ(),
      All("f", All("x", Var(0), Var(1)),
      All("x", Var(1),
      Var(2))))

TWO = Lam("P", Typ(),
      Lam("f", All("x", Var(0), Var(1)),
      Lam("x", Var(1),
      App(Var(1), App(Var(1), Var(0))))))

FOO = Lam("f", Typ(), Lam("x", Typ(), App(Var(1), App(Var(1), App(Var(1), Var(0))))))

term = TWO

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

print "Inferred:"
print term.infer(List()).to_string(List())
print ""
