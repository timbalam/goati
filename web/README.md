# myi
My language interpreter

An interpreter for a yet unnamed programming language by Tim Lamberton. See https://timbalam.github.io/language for tutorials and installation instructions.

Building this project requires [Haskell Stack](https://docs.haskellstack.org/en/stable/). The interpreter code is roughly divided as follows.
1. Parsing a syntax tree (see src/Parser.hs and src/Types/Parser.hs)
2. Checking and desugaring into a core expression (see src/Expr.hs and src/Types.Expr.hs)
3. Reducing the core expression (see src/Eval.hs)
4. Import resolution system (see src/Import.hs)
5. Library of commands gluing various combinations of these phases together (see src/Lib.hs)

Todo list for the project.
1. IO primitives and standard library
2. Documentation
3. Design and implement type inference to be done during checking phase
4. Benchmarking and optimisation
