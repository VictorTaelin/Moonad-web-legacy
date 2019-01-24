var formality = require("./formality.js");
var compiler = require("./compiler.js");

var example = `
  def the 
    [-T : Type]
    [x  : T]
    x

  -- Unit type

  def Unit @ self =
    {-Unit. : {self : Unit} Type}
    {void.  : (Unit. void)}
    (Unit. self)

  def void : Unit =
    [-Unit. : {self : Unit} Type]
    [void.  : (Unit. void)]
    void.

  -- Boolean

  def Bool @ self =
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

  def bool_ind
    [self   : Bool]
    [-Bool. : {self : Bool} Type]
    [true.  : (Bool. true)]
    [fals.  : (Bool. fals)]
    (~self -Bool. true. fals.)

  def not [b : Bool]
    (~b -([self : Bool] Bool) fals true)

  -- Natural numbers

  def Nat @ self = 
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

  def nat_ind
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

  def Eq [-A : Type] [a : A] [b : A] @ self =
    {-Eq.  : {-A : Type} {a : A} {b : A} {self : (Eq -A a b)} Type}
    {refl. : {-A : Type} {-t : A} (Eq. -A t t (refl -A -t))}
    (Eq. -A a b self)

  def refl [-A : Type] [-t : A] : (Eq -A t t) =
    [-Eq.  : {-A : Type} {a : A} {b : A} {self : (Eq -A a b)} Type]
    [refl. : {-A : Type} {-t : A} (Eq. -A t t (refl -A -t))]
    (refl. -A -t)

  def sym [-A : Type] [-a : A] [-b : A] [e : (Eq -A a b)]
    (~e -[-A : Type] [a : A] [b : A] [self : (Eq -A a b)] (Eq -A a b)
         [-A : Type] [-t : A]                             (refl -A -t))

  def cong [-A : Type] [-B : Type] [-a : A] [-b : A] [e : (Eq -A a b)]
    (~e -[-A : Type] [a : A] [b : A] [self : (Eq -A a b)] {-f : {x : A} B} (Eq -B (f a) (f b))
         [-A : Type] [-t : A]                             [-f : {x : A} B] (refl -B -(f t)))

  def subst [-A : Type] [-a : A] [-b : A] [e : (Eq -A a b)]
    (~e -[-A : Type] [a : A] [b : A] [self : (Eq -A a b)] {-P : {x : A} Type} {px : (P a)} (P b) 
         [-A : Type] [-t : A]                             [-P : {x : A} Type] [px : (P t)] px)

  -- Natural number theorems

  def add [a : Nat]
    let motive [self : Nat]
      {b : Nat} Nat
    let case_succ [-pred : Nat] [&pred : {b : Nat} Nat]
      [b : Nat] (succ (&pred b))
    let case_zero
      [b : Nat] b
    (~a -motive case_succ case_zero)

  -- ∀ n . n + 0 == n

  def add_n_zero [n : Nat]
    def motive [self : Nat]
      (Eq -Nat (add self zero) self)
    def case_succ [-pred : Nat] [&pred : (Eq -Nat (add pred zero) pred)]
      (cong -Nat -Nat -(add pred zero) -pred &pred -succ)
    def case_zero
      (refl -Nat -zero)
    (~n -motive case_succ case_zero)

  (the
    -{n : Nat}(Eq -Nat (add n zero) n)
    add_n_zero)
`;

var term = formality.parse(example);
console.log("Term:\n" + term.to_string() + "\n");
console.log("Type:\n" + term.check().eval(false, false).to_string() + "\n");
console.log("Eval:\n" + term.erase().eval(true, true).to_string() + "\n");

//console.log(":::::: Compiling to net :::::::\n");
//console.log("Term:\n" + compiler.decompile(compiler.compile(term, true)).to_string() + "\n");
//console.log("Norm:\n" + compiler.decompile(compiler.compile(term, true).reduce()[0]).to_string() + "\n");
//console.log("Rwts:\n" + compiler.compile(term, true).reduce()[1] + "\n");
