Goat language syntax
====================

This module defines and implements the syntax of the Goat programming language,
in the form of a Haskell domain specific language (DSL) encoded via a set of typeclasses.
The code is organised using a top-down approach,
so each of the moving parts is motivated before getting into the details.

See also module 'Goat.Lang.Parser' for a corresponding parser grammar.

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
it is an *assignment* with a left-hand side *pattern*.
In the second, it is a plain *path*.
A *pattern* can be a plain *path*,
a plain *pattern block*,
or a smaller *pattern* with an *extension* by a *pattern block*.

    // example *pattern*s
    a
    .b.c // *path*s
    { .a = b; c }
    { .a = { b; }; } // *pattern block*
    a { b } // *path* with *extension*
    
    // example *statement*s
    a = 1
    .b = 1
    a { .b = c } = d // *pattern* with *assignment*
    // (with rhs *definition*s)
    .f
    a.b // *path*

The DSL introduces a typeclass to represent overloaded *assignment* via operator ('#='),
and overloaded *extension* via operator ('#') 

> type Stmt_ s =
>   ( Assign_ s, Pattern_ (Lhs s)
>   , Path_ s
>   , Selects (Lhs s) ~ Selects s
>   , Key (Lhs s) ~ Key s
>   , Key (Selects s) ~ Key s
>   )
> type Pattern_ a =
>   ( Path_ a, PatternBlock_ a
>   , Extend_ a
>   , PatternBlock_ (Extension a)
>   , Item (Extension a) ~ Item a
>   , Rhs (Item a) ~ a
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

A *path* can have one of several forms. 
It can be a plain *identifier*,
a plain *field*,
or a (smaller) *path* with a *selection* by an *identifier*.

    // example *path*s
    a // *identifier*
    .b // *field*
    .b.f // *path* with *selection* with a *identifier*

The DSL introduces via typeclass an operator ('#.') for the  overloaded *select* operation.
The DSL represents a *field* as an overloaded empty string ('""') followed by a *select*. 

> type Path_ a =
>   ( Identifier_ a, Field_ a
>     -- Path_ (Selects a)
>   , Identifier_ (Selects a), Select_ (Selects a)
>   , Selects (Selects a) ~ Selects a
>   , Key (Selects a) ~ Key a
>   )
> type Field_ a = ( Select_ a, IsString (Selects a) )
> type Selector_ a =
>   ( Field_ a
>     -- Selector_ (Selects a)
>   , Select_ (Selects a)
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
The first form is an *assignment* with a left-hand side *selector*.
The second form is a plain *path*.

    // example *match statement*s
    .a = b
    .f.g =.a { b; } // *assignment* (with rhs *pattern*)
    a
    .f.g // *path*

The DSL utilises the overloaded operators for *assignment* and *extension* defined via 'Assign_' and 'Extend_' typeclasses.

> type MatchStmt_ a =
>   ( Assign_ a, Selector_ (Lhs a), Path_ a )

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
The DSL introduces overloaded operators corresponding to these *operation*s and *text literal*s via typeclass. 
  
> type Definition_ a =
>   ( Operator_ a, Field_ a, NumLiteral_ a
>   , TextLiteral_ a, Identifier_ a, Extend_ a
>   , Block_ a, Block_ (Extension a)
>   , Item (Extension a) ~ Item a
>   , Rhs (Item a) ~ a
>   , Selects a ~ a
>   )
> infixr 8 #^
> infixl 7 #*, #/
> infixl 6 #+, #-
> infix 4 #==, #!=, #<, #<=, #>, #>=
> infixr 3 #&&
> infixr 2 #||
> class Operator_ a where
>   (#||), (#&&), (#==), (#!=), (#>), (#>=), (#<), (#<=),
>     (#+), (#-), (#*), (#/), (#^) :: a -> a -> a
>   not_, neg_ :: a -> a
> class TextLiteral_ a where quote_ :: String -> a

Number
------

The Haskell DSL utilises the built-in overloaded numbers for *number literal*s,
via instances of the 'Num' and 'Fractional' typeclasses.

> type NumLiteral_ a = Fractional a

Comment
-------

The Haskell DSL introduces an overloaded operator for declaring comments via the 'Comment_' typeclass.
  
> infixr 0 #//
> class Comment_ r where
>   (#//) :: r -> String -> r


File
----

A Goat *file* can begin with a *preface*.
A *preface* optionally begins with an *import* section,
optionally followed by an *include* section*,
and finishes with a *module* section.
Alternatively, a *file* can be plain *block*.
An *import* section begins with an *extern keyword*,
followed by a *list* of *import statement*s.
An *include* section is an *include keyword* followed by an *identifier*.
A *module* section is a *module* keyword followed by a *block*.
An *import statement* is an *assignment* with a left-hand side *identifier* and right-hand side *text literal*.
The Haskell DSL introduces keywords for *import*,
*include* and *module* sections via typeclasses.

> type Preface_ r =
>   ( Block_ r, Imports_ r, ImportStmt_ (ImportItem r)
>   , Item (ModuleBody r) ~ Item r
>   )
> type ImportStmt_ s =
>   (Assign_ s, Identifier_ (Lhs s), TextLiteral_ (Rhs s))
> class Block_ (ModuleBody r) => Module_ r where
>   type ModuleBody r
>   module_ :: ModuleBody r -> r
> class 
>   ( Module_ r, Module_ (Includes r)
>   , Identifier_ (IncludeKey r)
>   , ModuleBody (Includes r) ~ ModuleBody r
>   ) => Include_ r where
>   type Includes r
>   type IncludeKey r
>   include_ :: IncludeKey r -> Includes r -> r
> class
>   ( Include_ r, Include_ (Imports r)
>   , ImportStmt_ (ImportItem r)
>   , ModuleBody (Imports r) ~ ModuleBody r
>   ) => Imports_ r where
>   type ImportItem r
>   type Imports r
>   extern_ :: [ImportItem r] -> Imports r -> r
