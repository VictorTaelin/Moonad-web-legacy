const nasic = require("./nasic.js");
const assert = require('assert');
const cedille = require("./cedille.js");

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

  def the [Unit : Type] [the : Unit] the

  -- Boolean type construction

  def CBool {-Bool : Type} {true : Bool} {fals : Bool} Bool
  def ctrue [-Bool : Type] [true : Bool] [fals : Bool] true
  def cfals [-Bool : Type] [true : Bool] [fals : Bool] fals

  def IBool [self : CBool] {-Bool : {b : CBool} Type} {true : (Bool ctrue)} {fals : (Bool cfals)} (Bool self)
  def itrue                [-Bool : {b : CBool} Type] [true : (Bool ctrue)] [fals : (Bool cfals)] true 
  def ifals                [-Bool : {b : CBool} Type] [true : (Bool ctrue)] [fals : (Bool cfals)] fals

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

  bool_induction
`;

var term = cedille(example);
assert(term.check().to_string() === "{b : Bool} {-P : {b : Bool} Type} {T : (P true)} {F : (P fals)} (P b)");
assert(term.eval().to_string() === "[b] [T] [F] (b T F)");
