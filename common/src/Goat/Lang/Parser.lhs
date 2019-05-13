Goat language grammar
=====================

The parser grammar of the Goat programming language is defined and implemented in three modules.
The modules also define translations to the Goat syntax defined in module 'Goat.Lang.Class'.

Module 'Goat.Lang.Parser.Block' defines the grammar for top-level blocks,
statements and definitions. 

Module 'Goat.Lang.Parser.Pattern' defines the grammar for patterns appearing on the left-hand side of block statements.

Module 'Goat.Lang.Parser.Path' defines the grammar for simple paths used for bindings.

This module reexports functions for parsing and showing Goat syntax and grammar.

> module Goat.Lang.Parser
>   ( module Goat.Lang.Parser.Block
>   , module Goat.Lang.Parser.Pattern
>   , module Goat.Lang.Parser.Path
>   ) where
> import Goat.Lang.Parser.Block
> import Goat.Lang.Parser.Pattern
> import Goat.Lang.Parser.Path