const nasic = require("./nasic.js");
const assert = require('assert');
const formality = require("./formality.js");

var net = new nasic.Net()
net.alloc_node(1);
net.alloc_node(2);
net.alloc_node(1);
net.alloc_node(1);
net.link_ports(new nasic.Pointer(0,0), new nasic.Pointer(0,2));
net.link_ports(new nasic.Pointer(0,1), new nasic.Pointer(3,2));
net.link_ports(new nasic.Pointer(1,0), new nasic.Pointer(2,0));
net.link_ports(new nasic.Pointer(1,1), new nasic.Pointer(3,0));
net.link_ports(new nasic.Pointer(1,2), new nasic.Pointer(3,1));
net.link_ports(new nasic.Pointer(2,1), new nasic.Pointer(2,2));
var rewrites = net.reduce()[1];
assert(rewrites === 3);

var net = new nasic.Net();
var a = net.alloc_node(0);
var b = net.alloc_node(0);
var c = net.alloc_node(1);
var d = net.alloc_node(0);
net.link_ports(new nasic.Pointer(a, 0), new nasic.Pointer(a, 2))
net.link_ports(new nasic.Pointer(a, 1), new nasic.Pointer(b, 0))
net.link_ports(new nasic.Pointer(b, 1), new nasic.Pointer(c, 2))
net.link_ports(new nasic.Pointer(b, 2), new nasic.Pointer(c, 1))
net.link_ports(new nasic.Pointer(c, 0), new nasic.Pointer(d, 0))
net.link_ports(new nasic.Pointer(d, 1), new nasic.Pointer(d, 2))
var rewrites = net.reduce()[1];
assert(rewrites === 2);

var net = new nasic.Net();
var a = net.alloc_node(0);
var b = net.alloc_node(0);
var c = net.alloc_node(0);
var d = net.alloc_node(0);
var e = net.alloc_node(1);
var f = net.alloc_node(0);
var g = net.alloc_node(0);
var h = net.alloc_node(0);
var i = net.alloc_node(2);
var j = net.alloc_node(0);
var k = net.alloc_node(0);
var l = net.alloc_node(0);
net.link_ports(new nasic.Pointer(a, 0), new nasic.Pointer(a, 2));
net.link_ports(new nasic.Pointer(a, 1), new nasic.Pointer(b, 2));
net.link_ports(new nasic.Pointer(b, 1), new nasic.Pointer(h, 0));
net.link_ports(new nasic.Pointer(b, 0), new nasic.Pointer(c, 0));
net.link_ports(new nasic.Pointer(c, 1), new nasic.Pointer(e, 0));
net.link_ports(new nasic.Pointer(c, 2), new nasic.Pointer(d, 0));
net.link_ports(new nasic.Pointer(d, 1), new nasic.Pointer(f, 1));
net.link_ports(new nasic.Pointer(d, 2), new nasic.Pointer(g, 2));
net.link_ports(new nasic.Pointer(e, 1), new nasic.Pointer(f, 0));
net.link_ports(new nasic.Pointer(e, 2), new nasic.Pointer(g, 0));
net.link_ports(new nasic.Pointer(f, 2), new nasic.Pointer(g, 1));
net.link_ports(new nasic.Pointer(h, 1), new nasic.Pointer(i, 0));
net.link_ports(new nasic.Pointer(h, 2), new nasic.Pointer(j, 0));
net.link_ports(new nasic.Pointer(i, 1), new nasic.Pointer(k, 0));
net.link_ports(new nasic.Pointer(i, 2), new nasic.Pointer(l, 0));
net.link_ports(new nasic.Pointer(j, 1), new nasic.Pointer(k, 1));
net.link_ports(new nasic.Pointer(j, 2), new nasic.Pointer(l, 2));
net.link_ports(new nasic.Pointer(k, 2), new nasic.Pointer(l, 1));
var rewrites = net.reduce()[1];
assert(rewrites === 14);

var example = `
  -- Unit
  def the [P : Type] [x : P]
    x

  -- Booleans
  data Bool : Type
  | true    : Bool
  | false   : Bool;

  -- Inducton on Bool
  def bool_induction
    [b : Bool]
    [P : {b : Bool} Type]
    [T : (P true)]
    [F : (P false)]
    ? Bool b -> (P self)
    | true   => T
    | false  => F ;

  -- Bool negation
  def not [b : Bool]
    ? Bool b -> Bool
    | true   => false
    | false  => true;

  -- Natural numbers
  data Nat : Type
  | succ   : {pred : Nat} Nat
  | zero   : Nat;

  -- Nat examples
  def n0 zero
  def n1 (succ n0)
  def n2 (succ n1)
  def n3 (succ n2)
  def n4 (succ n3)

  -- Nat induction
  def nat_induction
    [n  : Nat]
    [-P : {-n : Nat} Type]
    [S  : {-n : Nat} {p : (P -n)} (P -(succ n))]
    [Z  : (P -zero)]
    ? Nat n -> (P -self)
    | succ  => (S -pred ~pred)
    | zero  => Z ;

  -- Nat addition
  def add [a : Nat]
    ? Nat a -> {b : Nat} Nat
    | succ  => [b : Nat] (succ (~pred b))
    | zero  => [b : Nat] b ;

  -- Nat multiplication
  def mul [n : Nat] [m : Nat]
    ? Nat n -> Nat
    | succ  => (add m ~pred)
    | zero  => zero ;

  data Zup : {a : Bool} {b : Bool} Type
  | zip    : (Zup false true) 
  | zap    : (Zup true false) ;

  def zup_test
    ? Zup zip -> (? Bool b -> Type | true => Bool | false => Nat ;)
    | zip     => true
    | zap     => zero ;

  -- Example type indexed on Nat (just Vectors without elements)
  data Ind : {n : Nat} Type
  | step   : {-n : Nat} {i : (Ind n)} (Ind (succ n))
  | base   : (Ind zero) ;

  -- Ind examples
  def i0 base
  def i1 (step -n0 i0)
  def i2 (step -n1 i1)
  def i3 (step -n2 i2)
  def i4 (step -n3 i3)

  -- From Nat to Ind
  def nat_to_ind [n : Nat]
    ? Nat n -> (Ind self)
    | succ  => (step -pred ~pred)
    | zero  => base ;

  -- Equality
  data Eq : {-A : Type} {a : A} {b : A} Type
  | refl  : {-A : Type} {-t : A} (Eq -A t t) ;

  -- Symmetry of equality
  def sym [-A : Type] [-a : A] [-b : A] [e : (Eq -A a b)]
    ? Eq e -> (Eq -A b a)
    | refl => (refl -A -t) ;

  -- Congruence of equality
  def cong [-A : Type] [-B : Type] [-x : A] [-y : A] [e : (Eq -A x y)]
    ? Eq e -> {-f : {x : A} B} (Eq -B (f a) (f b))
    | refl => [-f : {x : A} B] (refl -B -(f t)) ;

  -- Substitution of equality
  def subst [-A : Type] [-x : A] [-y : A] [e : (Eq -A x y)]
    ? Eq e -> {-P : {x : A} Type} {px : (P a)} (P b)
    | refl => [-P : {x : A} Type] [px : (P t)] px ;

  -- n + 0 == n
  def add_n_zero [n : Nat]
    ? Nat n -> (Eq -Nat (add self zero) self)
    | succ  => (cong -Nat -Nat -(add pred zero) -pred ~pred -succ)
    | zero  => (refl -Nat -zero);

  -- n + S(m) == S(n + m)
  def add_n_succ_m [n : Nat]
    ? Nat n -> {m : Nat} (Eq -Nat (add self (succ m)) (succ (add self m)))
    | succ  => [m : Nat] (cong -Nat -Nat -(add pred (succ m)) -(succ (add pred m)) (~pred m) -succ)
    | zero  => [m : Nat] (refl -Nat -(succ m));

  [n : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat] (?($ Nat : Type | succ : {pred : Nat} Nat | zero : Nat ;) n -> {m : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat} {-Eq : {-A : Type} {a : A} {b : A} Type} {refl : {-A : Type} {-t : A} (Eq -A t t)} (Eq -{-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat ((?($ Nat : Type | succ : {pred : Nat} Nat | zero : Nat ;) self -> {b : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat} {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat | succ => [b : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat] [-Nat : Type] [succ : {pred : Nat} Nat] [zero : Nat] (succ (~pred b -Nat succ zero)) | zero => [b : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat] b ;) [-Nat : Type] [succ : {pred : Nat} Nat] [zero : Nat] (succ (m -Nat succ zero))) [-Nat : Type] [succ : {pred : Nat} Nat] [zero : Nat] (succ ((?($ Nat : Type | succ : {pred : Nat} Nat | zero : Nat ;) self -> {b : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat} {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat | succ => [b : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat] [-Nat : Type] [succ : {pred : Nat} Nat] [zero : Nat] (succ (~pred b -Nat succ zero)) | zero => [b : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat] b ;) m -Nat succ zero))) | succ => [m : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat] ((?($ Eq : {-A : Type} {a : A} {b : A} Type | refl : {-A : Type} {-t : A} (Eq -A t t) ;) (~pred m) -> {-f : {x : A} {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat} {-Eq : {-A : Type} {a : A} {b : A} Type} {refl : {-A : Type} {-t : A} (Eq -A t t)} (Eq -{-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat (f a) (f b)) | refl => [-f : {x : A} {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat] [-Eq : {-A : Type} {a : A} {b : A} Type] [refl : {-A : Type} {-t : A} (Eq -A t t)] (refl -{-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat -(f t)) ;) -[pred : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat] [-Nat : Type] [succ : {pred : Nat} Nat] [zero : Nat] (succ (pred -Nat succ zero))) | zero => [m : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat] [-Eq : {-A : Type} {a : A} {b : A} Type] [refl : {-A : Type} {-t : A} (Eq -A t t)] (refl -{-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat -[-Nat : Type] [succ : {pred : Nat} Nat] [zero : Nat] (succ (m -Nat succ zero))) ;)

  add_n_succ_m
`;

console.log(formality(example).eval(true).to_string());
assert(formality(example).check().eval().to_string() === "{n : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat} {m : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat} {-Eq : {-A : Type} {a : A} {b : A} Type} {refl : {-A : Type} {-t : A} (Eq -A t t)} (Eq -{-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat ((?($ Nat : Type | succ : {pred : Nat} Nat | zero : Nat ;) n -> {b : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat} {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat | succ => [b : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat] [-Nat : Type] [succ : {pred : Nat} Nat] [zero : Nat] (succ (~pred b -Nat succ zero)) | zero => [b : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat] b ;) [-Nat : Type] [succ : {pred : Nat} Nat] [zero : Nat] (succ (m -Nat succ zero))) [-Nat : Type] [succ : {pred : Nat} Nat] [zero : Nat] (succ ((?($ Nat : Type | succ : {pred : Nat} Nat | zero : Nat ;) n -> {b : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat} {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat | succ => [b : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat] [-Nat : Type] [succ : {pred : Nat} Nat] [zero : Nat] (succ (~pred b -Nat succ zero)) | zero => [b : {-Nat : Type} {succ : {pred : Nat} Nat} {zero : Nat} Nat] b ;) m -Nat succ zero)))");
