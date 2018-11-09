# goati-web
Goat interpreter compiled to Javascript

An interpreter for a programming language by Tim Lamberton. See https://timbalam.github.io/language for tutorials and installation instructions.

Building this project requires [Haskell Stack](https://docs.haskellstack.org/en/stable/). The bulk of the interpreter code is found in '../common'. In this repository 'app/Web.hs' contains code for defining the web-compatible interpreter compiled using the 'GHCJS' library.