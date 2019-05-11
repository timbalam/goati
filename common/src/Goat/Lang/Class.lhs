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

> type Block_ a = (IsList a, Stmt_ (Item a))

Statement
---------

A Goat *statement* has multiple syntactic forms.
In the first form,
it is an *assignment* with a left-hand side *pattern* and right-hand side *definition*.
In the second, it is a plain *path*.
A *pattern* can be a plain *path*,
a plain *pattern block*,
or a smaller *pattern* with an *extension* by a *pattern block*.
The DSL introduces a typeclass to represent overloaded *assignment* via operator ('#='),
and overloaded *extension* via operator ('#') 

> type Stmt_ a =
>   ( Path_ a, Assign_ a
>   , Pattern_ (Lhs a)
>   , Definition_ (Rhs a)
>   , Selects (Lhs a) ~ Selects a
>   , Key (Lhs a) ~ Key a
>   , Key (Selects a) ~ Key a
>   )
> class
>   ( Path_ a, IsList a, Extend_ a
>   , IsList (Extension a)
>   , Extends a ~ a
>   , Item a ~ Item (Extension a)
>     -- MatchStmt_ (Item a)
>   , Path_ (Item a), Assign_ (Item a)
>   , Selector_ (Lhs (Item a))
>   , Rhs (Item a) ~ a
>   ) => Pattern_ a
> {-
> type Pattern_ a =
>   ( Path_ a, IsList a, Extend_ a
>   , IsList (Extension a)
>   , Extends a ~ a
>   , Item a ~ Item (Extension a)
>     -- MatchStmt_ (Item a)
>   , Path_ (Item a), Assign_ (Item a)
>   , Selector_ (Lhs (Item a))
>   , Rhs (Item a) ~ a
>   )
> -}

> infix 1 #=
> class Assign_ a where
>   type Lhs a
>   type Rhs a
>   (#=) :: Lhs a -> Rhs a -> a

> infixl 9 #
> class Extend_ a where
>   type Extension a
>   type Extends a
>   (#) :: Extends a -> Extension a -> a

Path
----

A *path* is either an *identifier* or a *field*,
optionally followed by a *selector*.
A *selector* is sequence of *select*s.
The DSL introduces via typeclass an operator ('#.') for the  overloaded *select* operation.
The DSL represents a *field* as an overloaded empty string ('""') followed by a *select*. 

> type Field_ a = ( Select_ a, IsString (Selects a) )
> type Var_ a = (Field_ a, Identifier_ a)
> type Path_ a =
>   ( Identifier_ a, Selector_ a, Identifier_ (Selects a) )
> type Selector_ a =
>   ( Field_ a, Select_ (Selects a)
>   , Selects (Selects a) ~ Selects a
>   , Key (Selects a) ~ Key a
>   )

> infixl 9 #.
> class Identifier_ (Key a) => Select_ a where
>   type Selects a
>   type Key a
>   (#.) :: Selects a -> Key a -> a

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

> type PatternBlock_ a = (IsList a, MatchStmt_ (Item a))

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

> type MatchStmt_ a =
>   ( Path_ a, Assign_ a, Selector_ (Lhs a), Pattern_ (Rhs a) )

Definition
----------

A *definition* is an expression with several forms.
It can be a unary or binary *operation* of one or two (smaller) *definitions* respectively.
It can be a field *select* of a smaller *definition*. 
It can be a *definition* with an *extension* by a *block*.
It can be a *number literal*, *text literal*, *block*,
*identifier* or *field*.
An *operation* can be a binary *logical or*,
*logical and*, *equal*, *unequal*, *less than*,
*less or equal*, *greater than*, *greater or equal*,
*add*, *substract*, *multiply*, *divide*, or *power* operation,
or a unary *not* or *neg* operation.
The DSL introduces overloaded operator corresponding to these *operation*s and *text literal*s via typeclass. 

> class
>   ( Select_ a, Operator_ a, NumLiteral_ a, TextLiteral_ a
>   , Identifier_ a, Extend_ a, IsList_ a,
>   , Extension a ~ x, Extends a ~ e, Item a ~ i
>   , Selects a ~ s, Arg a ~ r
>   ) => Def_ a e x i s r | a -> e x i s r
>   
> type Definition_ a =
>   ( Field_ a, Operator_ a, NumLiteral_ a
>   , TextLiteral_ a, Identifier_ a, Extend_ a
>   , IsList a, IsList (Extension a)
>   , Item (Extension a) ~ Item a
>     -- Stmt_ (Item a)
>   , Path_ (Item a), Assign_ (Item a)
>   , Pattern_ (Lhs (Item a))
>   , Selects (Lhs (Item a)) ~ Selects (Item a)
>   , Key (Lhs (Item a)) ~ Key (Item a)
>   , Key (Selects (Item a)) ~ Key (Item a)
>     -- Definition_ (Arg a)
>   , Select_ (Arg a), Operator_ (Arg a), NumLiteral_ (Arg a)
>   , TextLiteral_ (Arg a), Identifier_ (Arg a), Extend_ (Arg a)
>   , IsList (Arg a)
>   , Extension (Arg a) ~ Extension a
>   , Extends (Arg a) ~ Extends a
>   , Item (Arg a) ~ Item a
>   , Selects (Arg a) ~ Selects a
>   , Arg (Arg a) ~ Arg a
>     -- Definition_ (Extends a)
>   , Select_ (Extends a), Operator_ (Extends a)
>   , NumLiteral_ (Extends a), TextLiteral_ (Extends a)
>   , Identifier_ (Extends a), Extend_ (Extends a)
>   , IsList (Extends a)
>   , Extension (Extends a) ~ Extension a
>   , Extends (Extends a) ~ Extends a
>   , Item (Extends a) ~ Item a
>   , Selects (Extends a) ~ Selects a
>   , Arg (Extends a) ~ Arg a
>     -- Definition_ (Selects a)
>   , Select_ (Selects a), Operator_ (Selects a)
>   , NumLiteral_ (Selects a), TextLiteral_ (Selects a)
>   , Identifier_ (Selects a), Extend_ (Selects a)
>   , IsList (Selects a)
>   , Extension (Selects a) ~ Extension a
>   , Extends (Selects a) ~ Extends a
>   , Item (Selects a) ~ Item a
>   , Selects (Selects a) ~ Selects a
>   , Arg (Selects a) ~ Arg a
>     -- Definition_ (Rhs (Item a))
>   , Select_ (Rhs (Item a)), Operator_ (Rhs (Item a))
>   , NumLiteral_ (Rhs (Item a)), TextLiteral_ (Rhs (Item a))
>   , Identifier_ (Rhs (Item a)), Extend_ (Rhs (Item a))
>   , IsList (Rhs (Item a))
>   , Extension (Rhs (Item a)) ~ Extension a
>   , Extends (Rhs (Item a)) ~ Extends a
>   , Item (Rhs (Item a)) ~ Item a
>   , Selects (Rhs (Item a)) ~ Selects a
>   , Arg (Rhs (Item a)) ~ Arg a
>   )
> infixr 8 #^
> infixl 7 #*, #/
> infixl 6 #+, #-
> infix 4 #==, #!=, #<, #<=, #>, #>=
> infixr 3 #&&
> infixr 2 #||
> class Operator_ a where
>   type Arg a
>   (#||), (#&&), (#==), (#!=), (#>), (#>=), (#<), (#<=),
>     (#+), (#-), (#*), (#/), (#^) :: Arg a -> Arg a -> a
>   not_, neg_ :: Arg a -> a
> class TextLiteral_ a where quote_ :: String -> a

Number
------

The Haskell DSL utilises the built-in overloaded numbers for *number literal*s,
via instances of the 'Num' and 'Fractional' typeclasses.

> type NumLiteral_ a = Fractional a

Comment
-------
  
> infixr 0 #//
> class Comment_ r where
>   (#//) :: r -> String -> r

