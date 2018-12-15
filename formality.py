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

    def to_net(self, net, var_ptrs):
        typ_addr = net.alloc_node(3)
        net.link_ports(Pointer(typ_addr, 1), Pointer(typ_addr, 1))
        net.link_ports(Pointer(typ_addr, 2), Pointer(typ_addr, 2))
        return Pointer(typ_addr, 0)

class All:
    def __init__(self, name, bind, body):
        self.name = name
        self.bind = bind
        self.body = body

    def to_string(self, scope):
        return "{" + self.name + " : " + self.bind.to_string(scope) + "} " + self.body.to_string(scope.prepend(self.name))

    def to_net(self, net, var_ptrs):
        all_addr = net.alloc_node(2)
        bind_ptr = self.bind.to_net(net, var_ptrs)
        net.link_ports(Pointer(all_addr, 1), bind_ptr)
        body_ptr = Lam(self.name, self.bind, self.body).to_net(net, var_ptrs)
        net.link_ports(Pointer(all_addr, 2), body_ptr)
        return Pointer(all_addr, 0)

class Lam: 
    def __init__(self, name, bind, body):
        self.name = name
        self.bind = bind
        self.body = body

    def to_string(self, scope):
        return "[" + self.name + " : " + self.bind.to_string(scope) + "] " + self.body.to_string(scope.prepend(self.name))

    # TODO cant do this because missing names, can't know what variable binds to what lambda
    def to_net(self, net, var_ptrs):
        lam_addr = net.alloc_node(1)
        tup_addr = net.alloc_node(1)
        net.link_ports(Pointer(lam_addr, 1), Pointer(lam_addr, 1))
        net.link_ports(Pointer(lam_addr, 0), Pointer(tup_addr, 2))
        bind_ptr = self.bind.to_net(net, var_ptrs)
        net.link_ports(Pointer(tup_addr, 1), bind_ptr)
        body_ptr = self.body.to_net(net, var_ptrs.prepend(Pointer(lam_addr, 1)))
        net.link_ports(Pointer(lam_addr, 2), body_ptr)
        return Pointer(tup_addr, 0)

class App:
    def __init__(self, func, argm):
        self.func = func
        self.argm = argm

    def to_string(self, scope):
        return "(" + self.func.to_string(scope) + " " + self.argm.to_string(scope) + ")"

    def to_net(self, net, var_ptrs):
        app_addr = net.alloc_node(1)
        tup_addr = net.alloc_node(1)
        net.link_ports(Pointer(tup_addr, 2), Pointer(app_addr, 0))
        net.link_ports(Pointer(tup_addr, 1), Pointer(tup_addr, 1))
        func_ptr = self.func.to_net(net, var_ptrs)
        net.link_ports(Pointer(tup_addr, 0), func_ptr)
        argm_ptr = self.argm.to_net(net, var_ptrs)
        net.link_ports(Pointer(app_addr, 1), argm_ptr)
        return Pointer(app_addr, 2)

class Var:
    def __init__(self, indx):
        self.indx = indx

    def to_string(self, scope):
        name = scope.get(self.indx)
        if name is not None:
            return name
        else:
            return "#" + str(self.indx - scope.len())

    def to_net(self, net, var_ptrs):
        ptr = var_ptrs.get(self.indx)
        if ptr is None:
            var_addr = net.alloc_node(self.indx + 1000 - var_ptrs.len())
            net.link_ports(Pointer(var_addr, 0), Pointer(var_addr, 2))
            return Pointer(var_addr, 1)
        else:
            return var_ptrs.get(self.indx)

class Cpy:
    def __init__(self, nam0, nam1, term, body):
        self.nam0 = nam0
        self.nam1 = nam1
        self.term = term
        self.body = body

    def to_string(self, scope):
        return "(TODO: copy to_string)"

    def to_net(self, net, var_ptrs):
        dup_addr = net.alloc_node(2000)
        net.link_ports(Pointer(dup_addr, 1), Pointer(dup_addr, 1))
        net.link_ports(Pointer(dup_addr, 2), Pointer(dup_addr, 2))
        term_ptr = self.term.to_net(net, var_ptrs)
        net.link_ports(term_ptr, Pointer(dup_addr, 0))
        body_ptr = self.body.to_net(net, var_ptrs.prepend(Pointer(dup_addr, 1)).prepend(Pointer(dup_addr, 2)))
        return body_ptr

def from_net(net, ptr, var_ptrs, dup_exit):
    label = net.nodes[ptr.addr].label

    # Lam / Var / App
    if label == 1:

        # Lam
        if ptr.port == 0:
            bind = from_net(net, net.enter_port(Pointer(ptr.addr, 1)), var_ptrs, dup_exit)
            ptr  = net.enter_port(Pointer(ptr.addr, 2))
            body = from_net(net, net.enter_port(Pointer(ptr.addr, 2)), var_ptrs.prepend(Pointer(ptr.addr, 1)), dup_exit)
            return Lam("x" + str(var_ptrs.len()), bind, body)

        # Var
        if ptr.port == 1:
            (indx, _) = var_ptrs.find(lambda p: p == ptr)
            return Var(indx)

        # App
        if ptr.port == 2:
            argm = from_net(net, net.enter_port(Pointer(ptr.addr, 1)), var_ptrs, dup_exit)
            ptr  = net.enter_port(Pointer(ptr.addr, 0))
            func = from_net(net, net.enter_port(Pointer(ptr.addr, 0)), var_ptrs, dup_exit)
            return App(func, argm)

    # All
    if label == 2:
        type = from_net(net, net.enter_port(Pointer(ptr.addr, 1)), var_ptrs, dup_exit)
        body = from_net(net, net.enter_port(Pointer(ptr.addr, 2)), var_ptrs, dup_exit).body
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
            print "dup 0"
            return from_net(net, net.enter_port(Pointer(ptr.addr, dup_exit.head)), var_ptrs, dup_exit.tail)
        else:
            #return Typ()
            return from_net(net, net.enter_port(Pointer(ptr.addr, 0)), var_ptrs, dup_exit.prepend(ptr.port))

def to_net(term):
    net = Net()
    root_addr = net.alloc_node(0)
    term_ptr = term.to_net(net, List())
    net.link_ports(Pointer(root_addr, 0), Pointer(root_addr, 2)) 
    net.link_ports(Pointer(root_addr, 1), term_ptr)
    return (net, term_ptr)

def reduce(term):
    (net, _) = to_net(term)
    net.reduce()
    term = from_net(net, net.enter_port(Pointer(0, 1)), List()) 
    return term

#BOOL  = All("P", Typ(), All("t", Typ(), All("f", Typ(), Var(2))))
#TRUE  = Lam("P", Typ(), Lam("t", Typ(), Lam("f", Typ(), Var(1))))
#FALSE = Lam("P", Typ(), Lam("t", Typ(), Lam("f", Typ(), Var(0))))
#NOT   = Lam("b", BOOL, App(App(App(Var(0), BOOL), FALSE), TRUE))

ID = Lam("P", Typ(), Lam("x", Var(0), Var(0)))

# (invalid, must copy P)
NAT = All("P", Typ(),
      All("f", All("x", Var(0), Var(1)),
      All("x", Var(1),
      Var(2))))

# (invalid, must copy P)
TWO = Lam("P", Typ(),
      Lam("f", All("x", Var(0), Var(1)),
      Lam("x", Var(1),
      Cpy("f0", "f1", Var(1),
      App(Var(0), App(Var(1), Var(2)))))))

term  = App(App(ID, NAT), TWO)

(net, ptr) = to_net(term)
#print net

print "Input term:"
print term.to_string(List())
print ""

print "Recovered form net:"
print from_net(net, net.enter_port(Pointer(0, 1)), List(), List()).to_string(List())
print ""

net.reduce()
#print net

print "Reduced:"
print from_net(net, net.enter_port(Pointer(0, 1)), List(), List()).to_string(List())
print ""
