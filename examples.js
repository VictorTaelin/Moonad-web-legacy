var formality = require("./formality.js");

var example = () => `
  _
  : (Type Type) 
  = (Type Type)

  the
  : {A : Type} {u : A} A
  = [A] [u] u

  -- The empty, uninhabited type

  Empty
  : {self : (Empty self)} Type
  = [self]
    {-Prop : {self : (Empty self)} Type}
    (Prop self)

  -- The unit type

  Unit
  : {self : (Unit self)} Type
  = [self]
    {-Prop : {self : (Unit self)} Type}
    {new   : (Prop Unit.new)}
    (Prop self)

  Unit.new
  : (Unit Unit.new)
  = [-Prop] [new] new

  -- The booleans true and false

  Bool
  : {self  : (Bool self)} Type
  = [self]
    {-Prop : {self : (Bool self)} Type}
    {true  : (Prop Bool.true)}
    {false : (Prop Bool.false)}
    (Prop self)

  Bool.true
  : (Bool Bool.true)
  = [-Prop] [true] [false] true

  Bool.false
  : (Bool Bool.false)
  = [-Prop] [true] [false] false

  Bool.induct
  : {self  : (Bool self)}
    {-Prop : {self : (Bool self)} Type}
    {true  : (Prop Bool.true)}
    {false : (Prop Bool.false)}
    (Prop self)
  = [self] [-Prop] [true] [false]
    (self -Prop true false)

  Bool.not
  : {self : (Bool self)} (Bool (Bool.not self))
  = [self]
    (self
      -[self](Bool (Bool.not self))
      Bool.false
      Bool.true)

  -- Natural numbers

  Nat
  : {self : (Nat self)} Type
  = [self]
    {-Prop : {self : (Nat self)} Type}
    {succ  : {-pred : (Nat pred)} {~pred : (Prop pred)} (Prop (Nat.succ pred))}
    {zero  : (Prop Nat.zero)}
    (Prop self)

  Nat.succ
  : {pred : (Nat pred)} (Nat (Nat.succ pred))
  = [pred] [-Nat.] [succ.] [zero.]
    (succ. -pred (pred -Nat. succ. zero.))

  Nat.zero
  : (Nat Nat.zero)
  = [-Nat.] [succ.] [zero.] zero.

  Nat.0 : (Nat Nat.0) = Nat.zero
  Nat.1 : (Nat Nat.1) = (Nat.succ Nat.0)
  Nat.2 : (Nat Nat.2) = (Nat.succ Nat.1)
  Nat.3 : (Nat Nat.3) = (Nat.succ Nat.2)
  Nat.4 : (Nat Nat.4) = (Nat.succ Nat.3)
  Nat.5 : (Nat Nat.5) = (Nat.succ Nat.4)
  Nat.6 : (Nat Nat.6) = (Nat.succ Nat.5)
  Nat.7 : (Nat Nat.7) = (Nat.succ Nat.6)
  Nat.8 : (Nat Nat.8) = (Nat.succ Nat.7)
  Nat.9 : (Nat Nat.9) = (Nat.succ Nat.8)

  Nat.induct
  : {self  : (Nat self)}
    {-Prop : {self : (Nat self)} Type}
    {succ  : {-pred : (Nat pred)} {~pred : (Prop pred)} (Prop (Nat.succ pred))}
    {zero  : (Prop Nat.zero)}
    (Prop self)
  = [self] [Prop] [succ] [zero]
    (self -Prop succ zero)

  Nat.id
  : {self : (Nat self)} (Nat (Nat.id self))
  = [self] [-Prop] [succ] [zero]
    (self -[self] (Prop (Nat.id self))
      [-pred : (Nat pred)] [pred. : (Prop (Nat.id pred))]
        (succ -(Nat.id pred) pred.)
      zero)

  Nat.double
  : {self : (Nat self)} (Nat (Nat.double self))
  = [self] [-Prop] [succ] [zero]
    (self -[self](Prop (Nat.double self))
      [-pred : (Nat pred)] [~pred : (Prop (Nat.double pred))]
        (succ -(Nat.succ (Nat.double pred)) (succ -(Nat.double pred) ~pred))
      zero)

  Nat.add
  : {a : (Nat a)} {b : (Nat b)} (Nat (Nat.add a b))
  = [a] [b] [-Prop] [succ] [zero]
    (a -[pred : (Nat pred)](Prop (Nat.add pred b))
      [-pred : (Nat pred)] [~pred : (Prop (Nat.add pred b))] (succ -(Nat.add pred b) ~pred)
      (b -[self](Prop (Nat.id self))
        [-pred : (Nat pred)] [~pred : (Prop (Nat.id pred))] (succ -(Nat.id pred) ~pred) 
        zero))

  -- Equality on self-referential types

  Eq
  : {-T   : {self : (T self)} Type}
    {a    : (T a)}
    {b    : (T b)}
    {self : (Eq -T a b self)}
    Type
  = [-T] [a] [b] [self]
    {-Prop : {b : (T b)} {self : (Eq -T a b self)} Type}
    {refl  : (Prop a (Eq.refl -T -a))}
    (Prop b self)

  Eq.refl
  : {-T : {self : (T self)} Type}
    {-a : (T a)}
    (Eq -T a a (Eq.refl -T -a))
  = [-T] [-a] [-Prop] [refl]
    refl

  Eq.sym
  : {-T : {self : (T self)} Type}
    {-a : (T a)}
    {-b : (T b)}
    {e  : (Eq -T a b e)}
    (Eq -T b a (Eq.sym -T -a -b e))
  = [-T] [-a] [-b] [e]
    (e -[b][self](Eq -T b a (Eq.sym -T -a -b self))
      (Eq.refl -T -a))

  Eq.cong
  : {-A : {self : (A self)} Type}
    {-B : {self : (B self)} Type}
    {-a : (A a)}
    {-b : (A b)}
    {e  : (Eq -A a b e)}
    {-f : {a : (A a)} (B (f a))}
    (Eq -B (f a) (f b) (Eq.cong -A -B -a -b e -f))
  = [-A] [-B] [-a] [-b] [e] [-f] 
    (e -[b][self](Eq -B (f a) (f b) (Eq.cong -A -B -a -b self -f))
      (Eq.refl -B -(f a)))

  Eq.subst
  : {-T : {self : (T self)} Type}
    {-a : (T a)}
    {-b : (T b)}
    {e  : (Eq -T a b e)}
    {-P : {a : (T a)} Type}
    {x  : (P a)}
    (P b)
  = [-T] [-a] [-b] [e] [-P] [x]
    (e -[b][self](P b) x)

  main
  = Eq.subst
`;

var defs = formality.parse(example());

var term = defs.main.term;
console.log("Term:\n" + formality.show(term) + "\n");

var norm = formality.norm(term, defs, true);

console.log("Norm (head):\n" + formality.show(formality.norm(formality.norm(term, defs, false), {}, true)) + "\n");
console.log("Norm (full):\n" + formality.show(formality.norm(term, defs, true)) + "\n");

try {
  var type = formality.infer(term, defs);
  console.log("Type:\n" + formality.show(formality.norm(type, {}, true)) + "\n");
} catch (e) {
  console.log("Type:");
  console.log(e);
  console.log("");
}
