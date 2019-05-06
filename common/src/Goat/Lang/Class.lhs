## Goat language syntax

This module defines and implements the syntax of the Goat programming language,
in the form of a Haskell domain specific language (DSL) encoded via a set of typeclasses.
The code is organised using a top-down approach,
so each of the moving parts is motivated before getting into the details.

See also 'src/Goat/Lang/Parser.lhs' for a corresponding parser grammar.

> module Goat.Lang.Class where
> import Data.These (These(..))
> import GHC.Exts (IsList(..))
> import Data.String (IsString)

### Block

Syntactically, a Goat *block* is a list of *statement*s.
The Goat Haskell DSL makes use of the built-in overloaded list syntax via the 'IsList' class instances.

> type Block_ a = (IsList a, Statement_ (Item a))

### Statement

A Goat *statement* has multiple syntactic forms.
The first starts with a *path*,
and can optionally omit the following *definition* to make a 'pun' form.
Alternatively, the *path* (optionally along with a *pattern*) be given a *defintion*.
In the third from we omit the *path* and give instead a *pattern* and *definition*.

> type Statement_ a =
>   ( Var_ a, Path_ (Compound a)
>   , Assign_ a, Var_ (Lhs a)
>   , Pattern_ (Lhs a), Definition_ (Rhs a)
>   , Compound (Lhs a) ~ Compound a
>   , Key (Lhs a) ~ Key a
>   , Key (Compound a) ~ Key a
>   )

For the DSL we introduce a typeclass for an overloaded assignment operator ('#='). 

> class Assign_ a where
>   type Lhs a
>   type Rhs a
>   (#=) :: Lhs a -> Rhs a -> a

### Pattern

A *pattern* is a sequence of *decompose block*s.

> type Pattern_ a =
>   ( Extend_ a
>   , DecomposeBlock_ a, DecomposeBlock_ (Extension a)
>   , Item a ~ Item (Extension a)
>   )

The DSL introduces an overloaded extension operator ('#') via typeclass

> class Extend_ a where
>   type Extension a
>   (#) :: a -> Extension a -> a

## Decompose block

Syntactically a *decompose block* is a sequence of *match statement*s. 

> type DecomposeBlock_ a = (IsList a, MatchStatement_ (Item a))


## Path

A *path* is either an *identifier* or a *field*,
optionally followed by a *selector*.
A *selector* is a sequence of *field*s.

> type Path_ a =
>   ( Identifier_ a, Selector_ a, Identifier_ (Compound a) )
> type Selector_ a =
>   ( Field_ a, Field_ (Compound a)
>   , Compound (Compound a) ~ Compound a
>   )

The DSL introduces via typeclass an overloaded field operator ('#.')

> class Identifier (Key a) => Field_ a where
>   type Compound a
>   type Key a
>   (#.) :: Compound a -> Key a -> a

## Identifier

An *identifier* is a character string.
The DSL uses the built-in overloaded string syntax via a 'IsString' class instance.

> type Identifier_ a = IsString a

## Definition

The DSL uses a canonical expression form introduced via overloaded operators via typeclass.


> class Operator_ a where
>   (#||), (#&&), (#==), (#!=), (#>), (#>=), (#<), (#<=),
>     (#+), (#-), (#*), (#/), (#^) :: r -> r -> r
>   not_, neg_ :: r -> r

## Number literal

> data DecimalFloat = DecimalFloat Integer Integer Integer
