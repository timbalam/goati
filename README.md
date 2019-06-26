goati
=====

Goat language interpreter
-------------------------

An interpreter for a programming language by Tim Lamberton.
See https://timbalam.github.io/language for tutorials and installation instructions.

Building this project requires [Haskell Stack](https://docs.haskellstack.org/en/stable/).
The bulk of the interpreter code is found in the './common' package,
roughly organised as follows.
1. A typeclass encoding of Goat's syntax in
'Goat.Lang.Class'
2. Parsers and printers for Goat's syntax in 
'Goat.Lang.Parser'
2. A core representation for optimisation, 
validation and interpretation in 'Goat.Repr'
5. Pipelines in 'Goat.Interpreter'

A test suite can be found in the 'test' directory of the package.

See also the 'native' and 'web' packages for compiled interpreters.

Todo list for the code base.
1. Design of IO and foreign code interfaces.
1. Finalise design and implement type inference to be done during checking phase
2. Benchmarking and optimisation
