var formality = require("./formality.js");
var compiler = require("./compiler.js");

var example = `
  def the 
    [-T : Type]
    [x  : T]
    x

  -- Unit type

  def Unit @ self :
    {-Unit. : {self : Unit} Type}
    {void.  : (Unit. void)}
    (Unit. self)

  def void : Unit =
    [-Unit. : {self : Unit} Type]
    [void.  : (Unit. void)]
    void.

  -- Boolean

  def Bool @ self :
    {-Bool. : {self : Bool} Type}
    {true.  : (Bool. true)}
    {fals.  : (Bool. fals)}
    (Bool. self)

  def true : Bool =
    [-Bool. : {self : Bool} Type]
    [true.  : (Bool. true)]
    [fals.  : (Bool. fals)]
    true.

  def fals : Bool =
    [-Bool. : {self : Bool} Type]
    [true.  : (Bool. true)]
    [fals.  : (Bool. fals)]
    fals.

  def bool_induction
    [self   : Bool]
    [-Bool. : {self : Bool} Type]
    [true.  : (Bool. true)]
    [fals.  : (Bool. fals)]
    (~self -Bool. true. fals.)

  def not [b : Bool]
    (~b -([self : Bool] Bool) fals true)

  -- Natural numbers

  def Nat @ self :
    {-Nat. : {self : Nat} Type}
    {succ. : {-pred : Nat} {&pred : (Nat. pred)} (Nat. (succ pred))}
    {zero. : (Nat. zero)}
    (Nat. self)

  def succ [pred : Nat] : Nat =
    [-Nat. : {self : Nat} Type]
    [succ. : {-pred : Nat} {&pred : (Nat. pred)} (Nat. (succ pred))]
    [zero. : (Nat. zero)]
    (succ. -pred (~pred -Nat. succ. zero.))

  def zero : Nat =
    [-Nat. : {self : Nat} Type]
    [succ. : {-pred : Nat} {&pred : (Nat. pred)} (Nat. (succ pred))]
    [zero. : (Nat. zero)]
    zero.

  def nat_induction
    [self  : Nat]
    [-Nat. : {self : Nat} Type]
    [succ. : {-pred : Nat} {&pred : (Nat. pred)} (Nat. (succ pred))]
    [zero. : (Nat. zero)]
    (~self -Nat. succ. zero.)

  def 0 zero
  def 1 (succ 0)
  def 2 (succ 1)
  def 3 (succ 2)
  def 4 (succ 3)

  -- Equality

  def Eq [-A : Type] [a : A] [b : A] @ self :
    {-Eq.  : {-A : Type} {a : A} {b : A} {self : (Eq -A a b)} Type}
    {refl. : {-A : Type} {-t : A} (Eq. -A t t (refl -A -t))}
    (Eq. -A a b self)

  def refl [-A : Type] [-t : A] : (Eq -A t t) =
    [-Eq.  : {-A : Type} {a : A} {b : A} {self : (Eq -A a b)} Type]
    [refl. : {-A : Type} {-t : A} (Eq. -A t t (refl -A -t))]
    (refl. -A -t)

  def symm [-A : Type] [-a : A] [-b : A] [e : (Eq -A a b)]
    (~e -[-A : Type] [a : A] [b : A] [self : (Eq -A a b)] (Eq -A b a)
         [-A : Type] [-t : A]                             (refl -A -t))

  def cong [-A : Type] [-B : Type] [-a : A] [-b : A] [e : (Eq -A a b)]
    (~e -[-A : Type] [a : A] [b : A] [self : (Eq -A a b)] {-f : {x : A} B} (Eq -B (f a) (f b))
         [-A : Type] [-t : A]                             [-f : {x : A} B] (refl -B -(f t)))

  def subs [-A : Type] [-a : A] [-b : A] [e : (Eq -A a b)]
    (~e -[-A : Type] [a : A] [b : A] [self : (Eq -A a b)] {-P : {x : A} Type} {x : (P a)} (P b) 
         [-A : Type] [-t : A]                             [-P : {x : A} Type] [x : (P t)] x)

  -- Natural number theorems

  def add [a : Nat]
    let motive [self : Nat]
      {b : Nat} Nat
    let case_succ [-pred : Nat] [&pred : {b : Nat} Nat]
      [b : Nat] (succ (&pred b))
    let case_zero
      [b : Nat] b
    (~a -motive case_succ case_zero)

  -- (add n 0) == n

  def add_n_zero [n : Nat]
    let motive [self : Nat]
      (Eq -Nat (add self zero) self)
    let case_succ [-pred : Nat] [&pred : (Eq -Nat (add pred zero) pred)]
      (cong -Nat -Nat -(add pred zero) -pred &pred -succ)
    let case_zero
      (refl -Nat -zero)
    (~n -motive case_succ case_zero)

  -- (add n (succ m)) = (succ (add n m))

  def add_n_succ_m [n : Nat]
    let motive [self : Nat]
      {-m : Nat} (Eq -Nat (add self (succ m)) (succ (add self m)))
    let case_succ [-n : Nat] [&n : (motive n)] [-m : Nat]
      (cong -Nat -Nat -(add n (succ m)) -(succ (add n m)) (&n -m) -succ)
    let case_zero
      [-m : Nat] (refl -Nat -(succ m))
    (~n -motive case_succ case_zero)

  -- (add n m) = (add m n)

  def add_comm [n : Nat]
    let motive [n : Nat]
      {m : Nat} (Eq -Nat (add n m) (add m n))
    let case_zero [m : Nat]
      (symm -Nat -(add m zero) -m (add_n_zero m))
    let case_succ [-n : Nat] [i : (motive n)] [m : Nat]
      let a (symm -Nat -(add n m) -(add m n) (i m))
      let b (add_n_succ_m m -n)
      let c (symm -Nat -(add m (succ n)) -(succ (add m n)) b)
      (subs -Nat -(add m n) -(add n m) a -[x : Nat](Eq -Nat (succ x) (add m (succ n))) c)
    (~n -motive case_succ case_zero)

  add_comm
`;

var term = formality.parse(example);

console.log("Term:\n" + term.to_string() + "\n");
try {
  console.log("Type:\n" + term.check().norm(false).to_string() + "\n");
} catch (e) {
  console.log("Type:\n" + e + "\n");
}
console.log("Norm (compact):\n" + term.head().norm(false).to_string(true) + "\n");
console.log("Norm (full):\n" + term.norm(true).to_string(true) + "\n");

//console.log(":::::: Compiling to net :::::::\n");
//console.log("Term:\n" + compiler.decompile(compiler.compile(term, true)).to_string() + "\n");
//console.log("Norm:\n" + compiler.decompile(compiler.compile(term, true).reduce()[0]).to_string() + "\n");
//console.log("Rwts:\n" + compiler.compile(term, true).reduce()[1] + "\n");
