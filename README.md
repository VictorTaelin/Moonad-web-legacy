## Moonad: a Peer-to-Peer Operating System

**Abstract.** A purely peer-to-peer implementation of an operating system should allow online applications to operate perpetually with no downtime. Ethereum partly solved that problem in 2014, but its focus on smart-contracts posed challenges for everyday adoption. Building upon its ideas, we present the design of a complete decentralized operating system. Our low-level machine language, Nasic, is inherently parallel and adequate for reducing high-order programs efficiently, in contrast to register and stack machines. Our high-level language, Cedille, is capable of exploiting Curry-Howard's isomorphism to verify security claims offline, allowing users to trust downloaded code without trusting its developers. An inductive datatype, DappSpec, is used to specify front-end user interfaces. A proof-of-work, tokenless blockchain, Ethernal, is used to aggregate and order global transactions, allowing applications to have a common back-end state. Our design is complete and final, making this a self-contained, timeless specification of the operating system. To facilitate independent implementations, each module is accompanied by commented Python code.

## 1. Nasic: a massively parallel, low-level machine language

### Motivation

Operating systems often make a distinction between high-level languages and low-level ones. This allows for a separation of concerns: while high-level languages tend to focus on usability and attempt to cater to human reasoning, low-level languages have only one job: being fast as possible. Those languages are often very similar to the underlying physical processor, which, for most modern computers, means register machines with assembly-like instructions. While that model has worked well for the last few decades, it clearly hit a bottleneck: the speed of CPUs has stagnated and programs aren't getting much faster [citation needed]. Nether less, our computing power keeps increasing exponentially if we take in consideration the rise of GPUs, FPGAs and ASICs. Problem is, programming for those architectures is still considered hard and niche. The culprit is our programming languages weren't built for massively parallel paradigms. Recently, encouraging promises were made by proponents of the functional paradigm, but those were never fully fulfied, mostly due to the inherent complexity of reducing lambda expressions. As of 2018, our programs are still sequential. The field is yet to find a satisfactory model for massively parallel programming.

In 1997, a very simple graph-rewrite system with only 3 symbols and 6 rules has been shown to be a universal model of computation [1]. This system is particularly interesting for its perfect computational properties. Like register machines, it can be evaluated as a series of atomic, local operations with a clear cost model. Like the λ-calculus, it is inherently parallel and has a nice logical interpretation. While, from the viewpoint of *computability*, those systems are equivalent (Turing complete), from the viewpoint of *computation*, interaction combinators is arguably superior, for being confluent and inherently parallel. In other words, while the Turing machine and other classical models can always be simulated by interaction combinators with no loss of efficiency, the converse isn't true. Despite that, this model has been mostly under the radar for the last two decades. We believe this is a mistake and, as such, designed an adaptation, n-ary symmetric interaction combinators (Nasic), as our low-level machine language. This allows our applications to natively run in a massively parallel model that, despite being so simple, is infinitely optimizable and extremelly powerful, thus, remarkably future-proof.

### Specification

Differently from conventional machine languages, which are usually described as bytecodes, Nasic programs are described as graphs in a specific format, which includes a single type of node with 3 outgoing edges and a symbolic label. That node is depicted below in a visual notation:

(image)

Any connected arrangement of those nodes forms a valid Nasic program. For example, those are valid Nasic programs:

(image)

Notice that the position of edges is important. For example, those graphs, while isomorphic, denote two different programs:

(image)

For that reason, the ports from which edges come are named. The port at the top of the triangle is the `main` port. The one nearest to it in counter-clockwise direction is the `aux1` port. The other one is the `aux2` port.

(image)

Moreover, there are 2 computation rules:

(image)

Those rewrite rules dictate that, whenever a sub-graph matches the left side of a rule, it must be replaced by its right side. For example, the graph below:

(image)

Is rewritten as:

(image)

Because (...). Rewritteable nodes are called redexes, or active pairs. 

This completes Nasic's specification. At this point, you might be questioning if such a simple graphical system can really replace Assembly and describe arbitrary programs that range from simple calculators to entire online games and social networks. While this may not be obvious or intuitive at first, rest assured the answer is yes. As argued by Lafont, interaction combinators capture the two fundamental rules of computation: annihilation and commutation. The first rule covers a wide array of computational phenomena such as communication, functions, datatypes, pattern-matching and garbage-collection. The second rule covers memory allocation, copying and repetitive behaviors such as loops and recursion. Together, they're not only Turing complete, but, one could argue, optimal in the context of classical computations. Parallelism comes naturally: in general, if two sub-expressions of your program could be reduced concurrently, they will. On the second section of this paper, it will become clear how common programming idioms translate to this model. For now, we'll focus in implementing it as described above. 

### Implementation


In our implementation, we will represent a Net as a table, where each row represents a Node, with its label, and 3 ports, each one including a Pointer to another port. As an example, consider the following net:

(image)

This could be represented as the following table:

addr | label | port 0 | port 1 | port 2
--- | --- | --- | --- | ---
0 | 0 | addr X, port X | addr X, port X | addr X, port X
1 | 0 | addr X, port X | addr X, port X | addr X, port X
2 | 1 | addr X, port X | addr X, port X | addr X, port X
3 | 0 | addr X, port X | addr X, port X | addr X, port X

For that, we use 3 classes: `Pointer`, holding an address and a port, `Node`, holding a node's label and ports, and `Net`, holding the table above, plus an array of active pairs, and reclaimable memory addresses. On the `Net` class, we implement 2 methods for space management: `alloc_node` and `free_node`, 3 methods for pointer wiring and navigation: `enter_port`, `link_ports` and `unlink_port`, and 2 methods for reductions: `rewrite` and `reduce`. A fully commented, executable example is available at [`nasic.py`](nasic.py). By importing this file, we're able to load the net above and reduce it:

```
net = Net.from_table(...)
```

This outputs the following table:

addr | label | port 0 | port 1 | port 2
--- | --- | --- | --- | ---
0 | 0 | addr X, port X | addr X, port X | addr X, port X
1 | 0 | addr X, port X | addr X, port X | addr X, port X
2 | 1 | addr X, port X | addr X, port X | addr X, port X
3 | 0 | addr X, port X | addr X, port X | addr X, port X

Which represents the reduced form of our graph:

(image)

### Performance considerations

While we've presented a complete Python implementation, it is clearly not the fastest one. In the short term, Nasic will not be competitive with standard compilers. In other of our implementations, though, we've observed promising performance characteristics. In ideal cases, Nasic managed to beat mature functional compilers such as GHC by orders of magnitude, due to optimal reductions and runtime fusion, which are unique to it. Even in worst cases, it didn't stand far behind, taking in account raw pattern-matches per second. Since those are early implementations, there are several possible improvements. 

A LLVM target with packed structures and no heap allocation would improve our rewrites per second. Simple optimizations such as prioritizing annihilations could keep the memory throughput lower. Native numeric operations could help, but we're not including them as part of the specification due to their complexity, and since they could hinder future optimizations. Nasic's inherent parallelism wasn't explored yet. GPU backends are promising, in special if they manage to use the shared memory of a streaming multiprocessor. Finally, proper miniaturization such as FPGAs and ASICs would make Nasic competitive with modern languages.

We leave it for client developers to creatively optimize their Nasic implementations as much as possible. 

## 2. Cedille: a high-level language for programs and proofs

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

## 4. Ethernal: a token-less blockchain for global transactions

## References

[1] https://pdfs.semanticscholar.org/6cfe/09aa6e5da6ce98077b7a048cb1badd78cc76.pdf
