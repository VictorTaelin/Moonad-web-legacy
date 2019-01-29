var formality = require("./formality.js");
var compiler = require("./compiler.js");

var example = `
  def the [-T : Type] [x  : T] x

  -- Empty type

  def Empty : Type = @self
    {-Empty. : {self : Empty} Type}
    (Empty. self)

  -- Unit type

  def Unit : Type = @self
    {-Unit. : {self : Unit} Type}
    {unit.  : (Unit. unit)}
    (Unit. self)

  def unit : Unit = $Unit
    [-Unit. : {self : Unit} Type]
    [unit.  : (Unit. unit)]
    unit.

  -- Boolean

  def Bool : Type = @self
    {-Bool. : {self : Bool} Type}
    {true.  : (Bool. true)}
    {fals.  : (Bool. fals)}
    (Bool. self)

  def true : Bool = $Bool
    [-Bool. : {self : Bool} Type]
    [true.  : (Bool. true)]
    [fals.  : (Bool. fals)]
    true.

  def fals : Bool = $Bool
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

  def not [b : Bool] : Bool = $Bool
    [-Bool. : {self : Bool} Type]
    [true.  : (Bool. true)]
    [fals.  : (Bool. fals)]
    (~b -[self : Bool](Bool. (not self)) fals. true.)

  -- Natural numbers

  def Nat : Type = @self
    {-Nat. : {self : Nat} Type}
    {succ. : ! {-pred : Nat} {pred. : (Nat. pred)} (Nat. (succ pred))}
    {zero. : ! (Nat. zero)}
    ! (Nat. self)

  def succ [pred : Nat] : Nat = $Nat
    [-Nat. : {self : Nat} Type]
    [succ. : ! {-pred : Nat} {pred. : (Nat. pred)} (Nat. (succ pred))]
    [zero. : ! (Nat. zero)]
    [succ. = succ.]
    [zero. = zero.]
    [pred. = (~pred -Nat. |succ. |zero.)]
    | (succ. -pred pred.)

  def zero : Nat = $Nat
    [-Nat. : {self : Nat} Type]
    [succ. : ! {-pred : Nat} {pred. : (Nat. pred)} (Nat. (succ pred))]
    [zero. : ! (Nat. zero)]
    [succ. = succ.]
    [zero. = zero.]
    | zero.

  def nat_induction
    [self  : Nat]
    [-Nat. : {self : Nat} Type]
    [succ. : ! {-pred : Nat} {&pred : (Nat. pred)} (Nat. (succ pred))]
    [zero. : ! (Nat. zero)]
    (~self -Nat. succ. zero.)

  def 0 zero
  def 1 (succ 0)
  def 2 (succ 1)
  def 3 (succ 2)
  def 4 (succ 3)

  def nat_id [self : Nat] : Nat = $Nat
    [-Nat. : {self : Nat} Type]
    [succ. : ! {-pred : Nat} {pred. : (Nat. pred)} (Nat. (succ pred))]
    [zero. : ! (Nat. zero)]
    [succ. = succ.]
    [zero. = zero.]
    (~self -[x:Nat](Nat. (nat_id x))
    | [-pred : Nat]
      [pred. : (Nat. (nat_id pred))]
      (succ. -(nat_id pred) pred.)
    | zero.)

  def add [a : Nat] [b : Nat] : Nat = $Nat
    [-Nat. : {self : Nat} Type]
    [succ. : ! {-pred : Nat} {pred. : (Nat. pred)} (Nat. (succ pred))]
    [zero. : ! (Nat. zero)]
    [succ. = succ.]
    [zero. = zero.]
    (~a -[x : Nat] (Nat. (add x b))
      | [-pred : Nat] [pred. : (Nat. (add pred b))] (succ. -(add pred b) pred.)
      (~b -[x:Nat](Nat. (nat_id x))
        | [-pred : Nat] [pred. : (Nat. (nat_id pred))] (succ. -(nat_id pred) pred.)
        | zero.))

  add

  ----------
  -- TODO --
  ----------

  def add ...

  def mul [a : Nat] [b : Nat]
    let motive [self : Nat]
      Nat
    let case_succ [-pred : Nat] [&pred : Nat]
      (add b &pred)
    let case_zero
      zero
    (~a -motive case_succ case_zero)

  -- Pair

  def Pair [-A : Type] [-B : Type] @ self :
    {-Pair. : {self : (Pair -A -B)} Type}
    {pair.  : {a : A} {b : B} (Pair. (pair -A -B a b))}
    (Pair. self)

  def pair [-A : Type] [-B : Type] [a : A] [b : B] : (Pair -A -B) =
    [-Pair. : {self : (Pair -A -B)} Type]
    [pair.  : {a : A} {b : B} (Pair. (pair -A -B a b))]
    (pair. a b)

  -- Equality

  def Eq [-A : Type] [a : A] [b : A] @ self :
    {-Eq.  : {b : A} {self : (Eq -A a b)} Type}
    {refl. : (Eq. a (refl -A -a))}
    (Eq. b self)

  def refl [-A : Type] [-a : A] : (Eq -A a a) =
    [-Eq.  : {b : A} {self : (Eq -A a b)} Type]
    [refl. : (Eq. a (refl -A -a))]
    refl.

  -- The J Axiom

  def symm [-A : Type] [-a : A] [-b : A] [e : (Eq -A a b)]
    (~e -[b : A] [self : (Eq -A a b)] (Eq -A b a) (refl -A -a))

  def cong [-A : Type] [-B : Type] [-a : A] [-b : A] [e : (Eq -A a b)]
    (~e -[b : A] [self : (Eq -A a b)] {-f : {x : A} B} (Eq -B (f a) (f b))
         [-f : {x : A} B] (refl -B -(f a)))

  def subs [-A : Type] [-a : A] [-b : A] [e : (Eq -A a b)]
    (~e -[b : A] [self : (Eq -A a b)] {-P : {x : A} Type} {x : (P a)} (P b) 
         [-P : {x : A} Type] [x : (P a)] x)

  -- Natural number theorems

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
  console.log("Type:");
  console.log(e);
  console.log("");
}

console.log("Norm (compact):\n" + term.head(true).norm(false).to_string(true) + "\n");

console.log("Norm (full):\n" + term.norm(true).to_string(true) + "\n");

console.log(":::::: Compiling to net :::::::\n");
console.log("Term:\n" + compiler.decompile(compiler.compile(term, false)).to_string() + "\n");
console.log("Norm:\n" + compiler.decompile(compiler.compile(term, false).reduce()[0]).to_string() + "\n");
console.log("Rwts:\n" + compiler.compile(term, false).reduce()[1] + "\n");
