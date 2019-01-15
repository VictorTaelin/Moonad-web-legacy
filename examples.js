var formality = require("./formality.js");

var example = `
  -- Congruence of equality

  def cong [-A : Type] [-B : Type] [-x : A] [-y : A] [-e : |x = y|] [-f : {x : A} B]
    (%k |(f x) = (f k)| e ($(f x) [x] x))

  -- Unit type

  def Unit {Unit : Type} {the : Unit} Unit
  def the  [Unit : Type] [the : Unit] the

  -- Example use of cong

  def cong_example [a : Unit] [b : Unit] [e : |a = b|]
    (cong -Unit -Unit -a -b -e -(the Unit))

  -- Boolean type construction

  def CBool
    {-Bool : Type}
    {true : Bool}
    {fals : Bool}
    Bool

  def ctrue
    [-Bool : Type]
    [true : Bool]
    [fals : Bool]
    true

  def cfals
    [-Bool : Type]
    [true : Bool]
    [fals : Bool]
    fals

  def IBool
    [self : CBool]
    {-Bool : {b : CBool} Type}
    {true : (Bool ctrue)}
    {fals : (Bool cfals)}
    (Bool self)

  def itrue
    [-Bool : {b : CBool} Type]
    [true : (Bool ctrue)]
    [fals : (Bool cfals)]
    true 

  def ifals
    [-Bool : {b : CBool} Type]
    [true : (Bool ctrue)]
    [fals : (Bool cfals)]
    fals

  def Bool <self : CBool> (IBool self)
  def true @self : (IBool self) = ctrue & itrue
  def fals @self : (IBool self) = cfals & ifals

  -- Proof of reflexivity: ∀ b. |(b true false) = b|

  def bool_reflection [b : Bool]
    def motive [b : CBool]|(b true fals) = b|
    (+b -motive ($ctrue ctrue) ($cfals cfals))

  -- Induction principle

  def bool_induction [b : Bool]
    [-P : {b : Bool} Type]
    [T  : (P true)]
    [F  : (P fals)]
    def motive [b : CBool](P (b -Bool true fals))
    (%x (P x) (bool_reflection b) (+b -motive T F))

  -- Natural number type construction

  def CNat
    {-CNat : Type}
    {zero  : CNat}
    {succ  : {x : CNat} CNat}
    CNat

  def csucc
    [n     : CNat]
    [-CNat : Type]
    [zero  : CNat]
    [succ  : {x : CNat} CNat]
    (succ (n -CNat zero succ))

  def czero
    [-CNat : Type]
    [zero  : CNat]
    [succ  : {x : CNat} CNat]
    zero

  def c0 (the CNat czero)
  def c1 (the CNat (csucc c0))
  def c2 (the CNat (csucc c1))
  def c3 (the CNat (csucc c2))
  def c4 (the CNat (csucc c3))

  def INat
    [x     : CNat]
    {-INat : {x : CNat} Type}
    {zero  : (INat czero)}
    {succ  : {-x : CNat} {n : (INat x)} (INat (csucc x))}
    (INat x)

  def isucc
    [-x    : CNat]
    [n     : (INat x)]
    [-INat : {x : CNat} Type]
    [zero  : (INat czero)]
    [succ  : {-x : CNat} {n : (INat x)} (INat (csucc x))]
    (succ -x (n -INat zero succ))

  def izero
    [-INat : {x : CNat} Type]
    [zero  : (INat czero)]
    [succ  : {-x : CNat} {n : (INat x)} (INat (csucc x))]
    zero

  def Nat <self : CNat> (INat self)
  def succ [n : Nat] @self : (INat self) = (csucc .n) & (isucc -.n +n)
  def zero @self : (INat self) = (the CNat czero) & izero

  def to_nat [x : CNat] (x -Nat zero succ)

  def nat_reflection [n : Nat]
    def motive [x : CNat]
      |.(to_nat x) = x|
    def case_z
      ($zero [x] x)
    def case_s [-x : CNat] [n : |.(to_nat x) = x|]
      (cong -CNat -CNat -.(to_nat x) -x -n -csucc)
    (+n -motive case_z case_s)

  def nat_induction
    [n : Nat]
    [P : {n : Nat} Type]
    [Z : (P zero)]
    [S : {-n : Nat} {i : (P n)} (P (succ n))]
    def motive [x : CNat]
      (P (to_nat x))
    def case_z
      Z
    def case_s [-x : CNat] [n : (P (to_nat x))]
      (S -(to_nat x) n)
    (%n (P n) (nat_reflection n) (+n -motive case_z case_s))

  nat_induction
`;

var term = formality(example);
console.log("Input:\n" + term.to_string() + "\n");
console.log("Normal:\n" + term.eval().to_string() + "\n");
console.log("Type:\n" + term.check().to_string() + "\n");
