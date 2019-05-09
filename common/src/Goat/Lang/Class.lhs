Goat language syntax
====================

This module defines and implements the syntax of the Goat programming language,
in the form of a Haskell domain specific language (DSL) encoded via a set of typeclasses.
The code is organised using a top-down approach,
so each of the moving parts is motivated before getting into the details.

See also 'src/Goat/Lang/Parser.lhs' for a corresponding parser grammar.

> {-# LANGUAGE TypeFamilies, ConstraintKinds, FlexibleContexts #-}
> module Goat.Lang.Class
>   (module Goat.Lang.Class, IsString(..), IsList (..))
> where
> import GHC.Exts (IsList(..))
> import Data.String (IsString(..))

Block
-----

Syntactically, a Goat *block* is a *list* of *statement*s.
The Goat Haskell DSL makes use of the built-in overloaded list syntax via 'IsList' class instances.

> type Block_ a = (IsList a, Statement_ (Item a))

Statement
---------

A Goat *statement* has multiple syntactic forms.
The general form is a *path* or a *pattern block*,
followed optionally by an intermediate sequence of *extension*s with *pattern block*s,
and ended by an *assignment* to a *definition*.
The other form is a lone *path*,
omiting the following *extensions*s and *assignment*.
The DSL introduces a typeclass to represent overloaded *assignment* via operator ('#='),
and overloaded *extension* via operator ('#') 

> type Statement_ a =
>   ( Path_ a, Assign_ a
>   , Pattern_ (Lhs a)
>   , Compound (Lhs a) ~ Compound a
>   , Key (Lhs a) ~ Key a
>   , Key (Compound a) ~ Key a
>   )
> type Pattern_ a =
>   ( Path_ a, PatternBlock_ a, Extend_ a
>   , PatternBlock_ (Extension a)
>   , Item a ~ Item (Extension a)
>   )

> infix 1 #=
> class Assign_ a where
>   type Lhs a
>   type Rhs a
>   (#=) :: Lhs a -> Rhs a -> a

> infixl 9 #
> class Extend_ a where
>   type Extension a
>   (#) :: a -> Extension a -> a

Path
----

A *path* is either an *identifier* or a *field*,
optionally followed by a *selector*.
A *selector* is sequence of *select*s.
The DSL introduces via typeclass an operator ('#.') for the  overloaded *select* operation.
The DSL represents a *field* as an overloaded empty string ('""') followed by a *select*. 

> type Field_ a = ( Select_ a, IsString (Compound a) )
> type Var_ a = (Field_ a, Identifier_ a)
> type Path_ a =
>   ( Identifier_ a, Selector_ a, Identifier_ (Compound a) )
> type Selector_ a =
>   ( Field_ a, Select_ (Compound a)
>   , Compound (Compound a) ~ Compound a
>   , Key (Compound a) ~ Key a
>   )

> infixl 9 #.
> class Identifier_ (Key a) => Select_ a where
>   type Compound a
>   type Key a
>   (#.) :: Compound a -> Key a -> a

Identifier
----------

An *identifier* is a character string.
The DSL uses the built-in overloaded string syntax via a 'IsString' class instance.

> type Identifier_ a = IsString a

Pattern block
-------------

Syntactically a *pattern block* is a *list* of *match statement*s. 
The DSL makes use of Haskell's built-in overloaded list syntax,
via instances of the 'IsList' typeclass.

> type PatternBlock_ a = (IsList a, MatchStatement_ (Item a))

Match statement
---------------

A *match statement* can have several forms.
The general form begins with a *selector*,
optionally followed by a *assignment* to a *pattern*.
The alternative form begins with an *identifier*,
optionally followed by a *selector*.
A *pattern* begins with either a *path* or a *pattern block*,
optionally followed by a sequence of *extensions* with *pattern block*s.
The DSL utilises the overloaded operators for *assignment* and *extension* defined via 'Assign_' and 'Extend_' typeclasses.

> type MatchStatement_ a =
>   ( Path_ a, Assign_ a, Selector_ (Lhs a) )

Definition
----------

A *definition* is an expression with several forms,
either one of several binary and unary *operation*s,
or a *select*, 
or an *extension* by a *block*,
or a *terminal* form.
A *terminal* form is either a *number literal*,
*text literal*, *block*, *identifier* or *field*.
An *operation* can be a binary *logical or*,
*logical and*, *equal*, *unequal*, *less than*,
*less or equal*, *greater than*, *greater or equal*,
*add*, *substract*, *multiply*, *divide*, or *power* operation,
or a unary *not* or *neg* operation.
The DSL introduces overloaded operator corresponding to these *operation*s and *text literal*s via typeclass. 

> type Definition_ a =
>   ( Def_ a, Selector_ a, Def_ (Compound a) )
> type Def_ a =
>   ( Operation_ a, Number_ a, Text_ a
>   , Block_ a, Extend_ a, Block_ (Extension a)
>   , Identifier_ a, Select_ a
>   , Item (Extension a) ~ Item a
>   )

> infixr 8 #^
> infixl 7 #*, #/
> infixl 6 #+, #-
> infix 4 #==, #!=, #<, #<=, #>, #>=
> infixr 3 #&&
> infixr 2 #||
> class Operation_ a where
>   (#||), (#&&), (#==), (#!=), (#>), (#>=), (#<), (#<=),
>     (#+), (#-), (#*), (#/), (#^) :: a -> a -> a
>   not_, neg_ :: a -> a
> class Text_ a where quote_ :: String -> a

Number
------

The Haskell DSL utilises the built-in overloaded numbers for *number literal*s,
via instances of the 'Num' and 'Fractional' typeclasses.

> type Number_ a = Fractional a

Comment
-------
  
> infixr 0 #//
> class Comment_ r where
>   (#//) :: r -> String -> r

