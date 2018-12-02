## Moon: a Peer-to-Peer Operating System

**Abstract.** A purely peer-to-peer implementation of an operating system should allow online applications to operate perpetually with no downtime. Ethereum partly solved that problem in 2014, but is limited to smart-contracts. Building upon its ideas, we present the design of a complete decentralized operating system. Our low-level machine language, Nasic, is inherently parallel and adequate for reducing high-order programs efficiently, in contrast to register and stack machines. Our high-level language, Formality, is capable of exploiting Curry-Howard's isomorphism to verify security claims offline, allowing users to trust downloaded code without trusting its developers. An inductive datatype, DappSpec, is used to specify front-end user interfaces. A proof-of-work, tokenless blockchain, Bitlog, is used to aggregate and order global transactions, allowing applications to have a common back-end state. Our design is complete and final, in the sense no further updates will ever be needed, making this a self-contained, timeless specification of the operating system. To facilitate independent implementations, each module is accompanied by commented Python code.

## 1. Nasic: a parallel, low-level machine language

A very simple graph-rewrite system with only 3 symbols and 6 rules has been shown to be a universal model of computation [1]. This system is particularly interesting for its perfect computational properties. Like a Turing machine, it is simple, powerful, and can be evaluated as a series of atomic, local operations. Like the λ-calculus, it is inherently high-order and has a nice logical interpretation. While, from the viewpoint of computability, the 3 systems are equivalent (Turing complete), from the viewpoint of computation, interaction combinators is arguably superior, for being confluent and inherently parallel. In other words, while the Turing machine and other classical models of computation can always be simulated by interaction combinators without loss of efficiency, the converse isn't true. That makes it perfectly architecture agnostic and future-proof. For that reason, Moon's low-level machine language is a slight adaptation that can be described as n-ary symmetric interaction combinators, or Nasic.

### Specification

Differently from conventional machine languages, which are usually described as bytecode, Nasic programs are described as graphs of a specific format. It includes exactly two types of nodes: Erasure nodes, which always have 1 outgoing edge, and Construction nodes, which always have 3 outgoing edges, plus a symbolic label. Below, Nasic's two node types are depicted in a visual notation:

(image)

Any connected arrangement of those nodes forms a valid Nasic program. For example, those are valid Nasic programs:

(image)

Notice that the position of edges is important. For example, those graphs, while isomorphic, denote two different programs:

(image)

For that reason, the slots from which edges come are named. The port at the top of the triangle is the `main` port. The one nearest to it in counter-clockwise direction is the `aux1` port. The other one is the `aux2` port.

(image)

Moreover, there are 3 computation rules:

(image)

Those rewrite rules dictate that, whenever a sub-graph matches the left side of a rule, it must be replaced by its right side. For example, the graph below:

(image)

Is rewritten as:

(image)

Because (...). Rewritteable nodes are called redexes, or active pairs. 

This completes Nasic's specification. At this point, you might be questioning if such a simple graphical system can really replace Assembly and describe arbitrary programs that range from simple calculators to entire online games and social networks. While this may not be obvious or intuitive at first, rest assured the answer is yes, as will become clear through the paper. For now, we'll shift our focus to just implementing such system, as described. 

### Implementation

Nasic's evaluation rules are well-defined, but its concrete implementation is up to the client developer. While our implementations has demonstrated satisfactory performance characteristics, which will be exposed later on, we believe that there is still a lot of room to explore. For example, Nasic's simplicity makes it adequate for massively parallel architectures such as the GPU, which we did not explore yet. Moreover, we hypothetize that, with proper miniaturization such as FPGAs and ASICs, Nasic processors could compete with, if not surpass, modern computer architectures in raw performance. For now, we'll build a reference Python implementation, for pedagogical purposes.

## 2. Formality: a high-level language for programs and proofs

types as a language of specifications

programs as mathematical proofs

### Description

### Implementation

## 3. DappSpec: a specification format for decentralized applications

```haskell
data Uint : Type
| O : (x : Uint) -> Uint
| I : (x : Uint) -> Uint
| Z : Uint

data List<A : Type> : Type
| cons : (x : A, xs : List) -> List
| nil  : List

data Element : Type
| circle : (x : Uint, y : Uint, r : Uint) -> Element
| square : (x : Uint, y : Uint, r : Uint) -> Element

let Document List<Element>

data LocalEvent : Type
| MouseClick : (x : Uint, y : Uint) -> LocalEvent
| Keypress   : (k : Uint)           -> LocalEvent

data App : Type
| new : 
  ( LocalState     : Type
  , local_inistate : LocalState
  , local_transact : (event : LocalEvent, state : LocalState) -> LocalState
  , render         : (state : LocalState) -> Document)
  -> App
```

## 4. Bitlog: a token-less blockchain for global transactions

## References

[1] https://pdfs.semanticscholar.org/6cfe/09aa6e5da6ce98077b7a048cb1badd78cc76.pdf
