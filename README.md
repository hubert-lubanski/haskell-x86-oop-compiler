# Native x86_64 Compiler & SSA Optimizer (Haskell)
**From Object-Oriented Syntax to Bare-Metal Assembly via Static Single Assignment**

This repository contains a fully functional compiler written in Haskell that translates an object-oriented, strongly-typed language directly into native x86_64 Assembly (NASM/ELF64). It completely bypasses intermediate frameworks like LLVM, handling low-level CPU architecture, register allocation, and assembly generation entirely from scratch.

## Architectural Highlights
* **Static Single Assignment (SSA) Infrastructure:** Transforms the intermediate representation into strict SSA form, computing dominance frontiers and injecting Phi functions to explicitly model data flow.
* **Custom Back-End Generation:** Operates directly on the x86_64 ABI. Maps abstract syntax and virtual variables directly to hardware instructions, completely eliminating high-level software abstraction layers.
* **Bare-Metal Object Orientation (VMTs):** Implements dynamic dispatch and polymorphism natively in assembly by manually calculating object memory layouts and generating custom Virtual Method Tables (VMT) stored in the `.rodata` section.

## Post-Mortem & Technical Debt
This project served as my primary vehicle for learning both the Haskell programming language and low-level compiler architecture. Consequently, the latter phases of the pipeline suffer from significant technical debt, missing optimizations, and architectural shortcuts taken to meet strict delivery constraints:

* **Unexploited SSA Form (Missing GCSE/LCSE):** The compiler pays the heavy structural cost of constructing a complete SSA graph (Dominance Frontiers, Phi nodes) but fails to capitalize on it. Critical optimization passes—specifically Global/Local Common Subexpression Elimination (GCSE/LCSE), Constant Propagation, and aggressive Dead Code Elimination—are not implemented.
* **Suboptimal Register Allocation:** Instead of utilizing rigorous interference graph coloring algorithms (e.g., Chaitin's), the register allocator relies on a naive, greedy heuristic. This results in highly inefficient spilling to the stack during periods of high register pressure, severely degrading potential L1 cache performance.
* **Over-engineered Haskell Constructs:** As an early Haskell project, the SSA generation logic is verbose and structurally complex. It lacks the idiomatic elegance of advanced Monad Transformers and functional folds, resulting in a bloated codebase that is difficult to refactor.
* **No Garbage Collection:** The language semantics support complex heap allocations via custom wrappers, but the runtime lacks any Garbage Collector or manual deallocation mechanics, resulting in continuous memory leaks during execution.
