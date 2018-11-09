# goati
Goat language interpreter

An interpreter for a programming language by Tim Lamberton. See https://timbalam.github.io/language for tutorials and installation instructions.

Building this project requires [Haskell Stack](https://docs.haskellstack.org/en/stable/). The interpreter code is roughly organised as follows.
1. A set of typeclasses encoding Goat's syntax (see src/Goat/Types/Syntax/Class.hs)
2. A parser (see src/Goat/Syntax/Parser.hs)
3. Two forms of core expressions (see src/Goat/Types/Expr.hs and src/Goat/Types/Eval.hs)
4. IO primitives (see src/Goat/Eval/IO.hs)
5. Pipeline (see src/Goat/Interpreter.hs)

Todo list for the code base.
1. Finalise design and implement import resolution system
1. Finalise design and implement type inference to be done during checking phase
2. Benchmarking and optimisation
