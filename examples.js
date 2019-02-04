var formality = require("./formality.js");
var compiler = require("./compiler.js");

var example = `
<<<<<<< Updated upstream
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
    (~a -[pred : Nat] (Nat. (add pred b))
      | [-pred : Nat] [pred. : (Nat. (add pred b))] (succ. -(add pred b) pred.)
      (~b -[b : Nat] (Nat. (nat_id b))
        | [-b : Nat] [b. : (Nat. (nat_id b))] (succ. -(nat_id b) b.)
        | zero.))

  -- Equality

  def Eq [-A : Type] [a : A] [b : A] : Type = @self
    {-Eq.  : {b : A} {self : (Eq -A a b)} Type}
    {refl. : (Eq. a (refl -A -a))}
    (Eq. b self)

  def refl [-A : Type] [-a : A] : (Eq -A a a) = $(Eq -A a a)
    [-Eq.  : {b : A} {self : (Eq -A a b)} Type]
    [refl. : (Eq. a (refl -A -a))]
    refl.

  def symm [-A : Type] [-a : A] [-b : A] [e : (Eq -A a b)]
    (~e -[b : A] [self : (Eq -A a b)] (Eq -A b a) (refl -A -a))

  def cong [-A : Type] [-B : Type] [-a : A] [-b : A] [e : (Eq -A a b)]
    (~e -[b : A] [self : (Eq -A a b)] {-f : {x : A} B} (Eq -B (f a) (f b))
         [-f : {x : A} B] (refl -B -(f a)))

  def subs [-A : Type] [-a : A] [-b : A] [e : (Eq -A a b)]
    (~e -[b : A] [self : (Eq -A a b)] {-P : {x : A} Type} {x : (P a)} (P b) 
         [-P : {x : A} Type] [x : (P a)] x)

  -- Nat theorems

  def add_n_zero [n : Nat]
    (~n -[self : Nat](Eq -Nat (add self zero) self)
    | [-pred : Nat] [&pred : (Eq -Nat (add pred zero) pred)]
      (cong -Nat -Nat -(add pred zero) -pred &pred -succ)
    | (refl -Nat -zero))

  def add_n_succ_m [n : Nat]
    let motive [self : Nat]
      {-m : Nat} (Eq -Nat (add self (succ m)) (succ (add self m)))
    let case_succ [-pred : Nat] [pred. : (motive pred)] [-m : Nat]
      (cong -Nat -Nat -(add pred (succ m)) -(succ (add pred m)) (pred. -m) -succ)
    let case_zero
      [-m : Nat] (refl -Nat -(add zero (succ m)))
    (~n -motive |case_succ |case_zero)

  def add_comm [n : Nat]
    let motive [n : Nat]
      {-m : Nat} !(Eq -Nat (add n m) (add m n))
    let case_zero [-m : Nat]
      | (refl -Nat -(add zero m))
    let case_succ [-n : Nat] [i : (motive n)] [-m : Nat]
      [k = (add_n_succ_m m)]
      [l = (i -m)]
      | let a (symm -Nat -(add n m) -(add m n) l)
        let b (k -n)
        let c (symm -Nat -(add m (succ n)) -(succ (add m n)) b)
        let d (subs -Nat -(add m n) -(add n m) a)
        (d -[x : Nat](Eq -Nat (succ x) (add m (succ n))) c)
    (~n -motive |case_succ |case_zero)

  add_comm
=======
the
: {A : Type} {u : A} A
= [A : Type] [u : A] u

Bool
: {self : (Bool self)} Type
= [self : (Bool self)]
  {-Bool. : {self : (Bool self)} Type}
  {true.  : (Bool. true)}
  {fals.  : (Bool. fals)}
  (Bool. self)

true
: (Bool true)
= [-Bool. : {self : (Bool self)} Type]
  [true.  : (Bool. true)]
  [fals.  : (Bool. fals)]
  true.

fals
: (Bool fals)
= [-Bool. : {self : (Bool self)} Type]
  [true.  : (Bool. true)]
  [fals.  : (Bool. fals)]
  fals.

bool_induction
: {self  : (Bool self)}
  {-Bool. : {self : (Bool self)} Type}
  {true.  : (Bool. true)}
  {fals.  : (Bool. fals)}
  (Bool. self)
= [self  : (Bool self)]
  [-Bool. : {self : (Bool self)} Type]
  [true.  : (Bool. true)]
  [fals.  : (Bool. fals)]
  (self -Bool. true. fals.)

not
: {self : (Bool self)} (Bool (not self))
= [self : (Bool self)] (self -[self : (Bool self)] (Bool (not self)) fals true)

main
= (the (Bool true) (not (not (not (not true)))))
>>>>>>> Stashed changes
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

console.log("Norm (compact):\n" + term.head(true).norm(false).erase().to_string() + "\n");

console.log("Norm (full):\n" + term.norm(true).norm(true).erase().to_string() + "\n");

//console.log(":::::: Compiling to net :::::::\n");
//console.log("Term:\n" + compiler.decompile(compiler.compile(term, false)).to_string() + "\n");
//console.log("Norm:\n" + compiler.decompile(compiler.compile(term, false).reduce()[0]).to_string() + "\n");
//console.log("Rwts:\n" + compiler.compile(term, false).reduce()[1] + "\n");
