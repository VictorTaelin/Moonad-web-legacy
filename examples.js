var formality = require("./formality.js");
var compiler = require("./compiler.js");

var example = `
  -- Congruence of equality

  def cong [-A : Type] [-B : Type] [-x : A] [-y : A] [-e : |x = y|] [-f : {x : A} B]
    (%k |(f x) = (f k)| e ($(f x) [x] x))

  -- Unit type

  def Unit {-Unit : Type} {the : Unit} Unit
  def the  [-Unit : Type] [the : Unit] the

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

  def not [a : CBool]
    [-Bool : Type]
    [true : Bool]
    [fals : Bool]
    (a -Bool fals true)

  def Bool <self : CBool>
    {-Bool : {b : CBool} Type}
    {true : (Bool ctrue)}
    {fals : (Bool cfals)}
    (Bool self)

  def true : Bool = ctrue &
    [-Bool : {b : CBool} Type]
    [true : (Bool ctrue)]
    [fals : (Bool cfals)]
    true

  def fals : Bool = cfals &
    [-Bool : {b : CBool} Type]
    [true : (Bool ctrue)]
    [fals : (Bool cfals)]
    fals

  -- Proof of reflexivity: ∀ b. |(b true false) = b|

  def bool_reflection [b : Bool]
    let motive [b : CBool]|(b true fals) = b|
    let case_t ($ctrue ctrue)
    let case_f ($cfals cfals)
    (+b -motive case_t case_f)

  -- Induction principle

  def bool_induction [b : Bool]
    [-P : {b : Bool} Type]
    [T  : (P true)]
    [F  : (P fals)]
    let motive [b : CBool](P (b -Bool true fals))
    let case_t T
    let case_f F
    (%x (P x)
      (bool_reflection b)
      (+b -motive case_t case_t))

  -- Natural numbers

  def Nat
    {-Nat : Type}
    {succ : !{x : Nat} Nat}
    ! {zero : Nat}
      Nat

  def succ
    [n    : Nat]
    [-Nat : Type]
    [succ : !{x : Nat} Nat]
    dup S succ
    dup N (n -Nat #S)
    # [zero : Nat]
      (S (N zero))

  def zero
    [-Nat : Type]
    [succ : !{x : Nat} Nat]
    # [zero : Nat]
      zero

  def nat_id [n : Nat] 
    [-Nat : Type]
    [succ : !{x : Nat} Nat]
    dup N (n -Nat succ)
    # [zero : Nat]
      (N zero)

  def n0 (the -Nat zero)
  def n1 (the -Nat (succ n0))
  def n2 (the -Nat (succ n1))
  def n3 (the -Nat (succ n2))
  def n4 (the -Nat (succ n3))

  -- Inductive hypothesis on natural numbers

  def Ind <self : Nat>
    {-Ind : {n : Nat} Type}
    {step : ! {-n : Nat} {i : (Ind n)} (Ind (succ n))}
    ! {base : (Ind zero)}
      (Ind self)

  def step [n : Ind] : Ind = (succ .n) &
    [-Ind : {n : Nat} Type]
    [step : ! {-n : Nat} {i : (Ind n)} (Ind (succ n))]
    dup S step
    dup N (+n -Ind #S)
    # [base : (Ind zero)]
      (S -.n (N base))

  def base : Ind = zero &
    [-Ind : {n : Nat} Type]
    [step : ! {-n : Nat} {i : (Ind n)} (Ind (succ n))]
    # [base : (Ind zero)]
      base

  def to_ind [n : Nat] 
    dup N (n -Ind #step) # (N base)

  def i0 (to_ind n0)
  def i1 (to_ind n1)
  def i2 (to_ind n2)
  def i3 (to_ind n3)
  def i4 (to_ind n3)

  (the -{x:Nat}!Ind to_ind)

  -- TODO: is it possible to implement (to_ind : {x : Nat} Ind)?
  -- TODO: migrade from here below

  def ind_reflection [i : Ind]
    let motive [n : Nat]
      |.(to_ind n) = n|
    let case_s [-n : Nat] [i : |.(to_ind n) = n|]
      (cong -Nat -Nat -.(to_ind n) -n -i -succ)
    let case_z
      ($zero [x] x)
    (+i -motive case_s case_s)

  ind_reflection

  def ind_induction
    [i  : Ind]
    [-P : {i : Ind} Type]
    [Z  : (P base)]
    [S  : {-i : Ind} {ih : (P i)} (P (step i))]
    let motive [n : Nat]
      (P (to_ind n))
    let case_z
      Z
    let case_s [-n : Nat] [ih : (P (to_ind n))]
      (S -(to_ind n) ih)
    (%i (P i) (ind_reflection i) (+i -motive case_z case_s))

  def add [n : Ind]
    let motive [n : Ind] {m : Ind} Ind
    let case_s [-n : Ind] [i : {m : Ind} Ind] [m : Ind] (step (i m)) 
    let case_z [m : Ind] m
    (ind_induction n -motive case_z case_s)

  def add_n_zero [n : Ind]
    let motive [n : Ind]
      |(add n zero) = n|
    let case_z
      $base base
    let case_s [-n : Ind] [i : (motive n)]
      (cong -Ind -Ind -(add n base) -n -i -step)
    (ind_induction n -motive case_z case_s)

  def add_n_succ_m [n : Ind]
    let motive [n : Ind]
      {m : Ind} |(add n (step m)) = (step (add n m))|
    let case_z [m : Ind]
      $(step m) (step m)
    let case_s [-n : Ind] [i : (motive n)] [m : Ind]
      (cong -Ind -Ind -(add n (step m)) -(step (add n m)) -(i m) -step)
    (ind_induction n -motive case_z case_s)

  def Pair
    [A : Type]
    [B : {a : A} Type]
    {Pair : Type}
    {new : {a : A} {b : (B a)} Pair}
    Pair

  def new
    [A : Type]
    [B : {a : A} Type]
    [a : A]
    [b : (B a)]
    [Pair : Type]
    [new : {a : A} {b : (B a)} Pair]
    (new a b)

  def Sigma
    [A : Type]
    [B : {a : A} Type]
    <self : (Pair A B)>
    {Sigma : {self : (Pair A B)} Type}
    {exist : {a : A} {b : (B a)} (Sigma (new A B a b))}
    (Sigma self)

  def exist
    [A : Type]
    [B : {a : A} Type]
    [a : A]
    [b : (B a)]
    : (Sigma A B)
    = (new A B a b)
    & [Sigma : {self : (Pair A B)} Type]
      [exist : {a : A} {b : (B a)} (Sigma (new A B a b))]
      (exist a b)

  def base : Ind = zero &
    [-Ind : {n : Nat} Type]
    [base : (Ind zero)]
    [step : {-n : Nat} {i : (Ind n)} (Ind (succ n))]
    base

  def step [n : Ind] : Ind = (succ .n) &
    [-Ind : {n : Nat} Type]
    [base : (Ind zero)]
    [step : {-n : Nat} {i : (Ind n)} (Ind (succ n))]
    (step -.n (+n -Ind base step))
    
  def add_comm [n : Ind]
    let motive [n : Ind]
      {m : Ind} |(add n m) = (add m n)|
    let case_z [m : Ind]
      ~(add_n_zero m)
    let case_s [-n : Ind] [i : (motive n)] [m : Ind]
      Type
    (nat_induction n -motive case_z case_s)

  add_comm
`;

var term = formality.parse(example);
console.log("Term:\n" + term.to_string() + "\n");
console.log("Norm:\n" + term.eval().to_string() + "\n");
console.log("Type:\n" + term.check().to_string() + "\n");
console.log(":::::: Compiling to net :::::::\n");
console.log("Term:\n" + compiler.decompile(compiler.compile(term)).to_string() + "\n");
console.log("Norm:\n" + compiler.decompile(compiler.compile(term).reduce()[0]).to_string() + "\n");
console.log("Rwts:\n" + compiler.compile(term).reduce()[1] + "\n");
