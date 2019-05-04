# goati
## Goat language interpreter

An interpreter for a programming language by Tim Lamberton. See https://timbalam.github.io/language for tutorials and installation instructions.

Building this project requires [Haskell Stack](https://docs.haskellstack.org/en/stable/). The interpreter code is roughly organised as follows.
1. A typeclass encoding of Goat's syntax (see src/Goat/Lang/Class)
2. A effect-style encoding of Goat's syntax via a free monad over an open union of concrete types (see src/Goat/Lang/Eff)
2. Parsers and printers for Goat's syntax (see src/Goat/Lang/Parser)
2. A core representation for optimisation, validation and interpretation (see src/Goat/Repr)
4. IO primitives (see src/Goat/Repr/IO)
5. Pipeline (see src/Goat/Interpreter)

Todo list for the code base.
1. Finalise design and implement import resolution system
1. Finalise design and implement type inference to be done during checking phase
2. Benchmarking and optimisation
