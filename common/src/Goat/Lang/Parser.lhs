Goat language grammar
=====================

The parser grammar of the Goat programming language is defined and implemented in three modules.
The modules also define translations to the Goat syntax defined in module 'Goat.Lang.Class'.

Module 'Goat.Lang.Parser.Block' defines the grammar for top-level blocks,
statements and definitions. 

Module 'Goat.Lang.Parser.Pattern' defines the grammar for patterns appearing on the left-hand side of block statements.

Module 'Goat.Lang.Parser.Path' defines the grammar for simple paths used for bindings.

Module 'Goat.Lang.Parser.Preface' defines the grammar for a Goat source preface.

Module 'Goat.Lang.Parser.Token' defines simple tokens for the Goat parser.

This module reexports functions for parsing and showing Goat syntax and grammar.

> module Goat.Lang.Parser
>   ( -- block
>     BLOCK, block, parseBlock, showBlock, toBlock
>   , -- statement
>     STMT, stmt, parseStmt, showStmt
>   , toStmt, CanonStmt_(..), CanonStmt
>   , -- definition
>     DEFINITION, definition, parseDefinition
>   , showDefinition
>   , toDefinition, unself, CanonExpr_(..)
>   , CanonExpr, CanonDefinition
>   , -- pattern
>     PATTERN, pattern, parsePattern, showPattern
>   , toPattern, CanonPattern(..)
>   , -- pattern block
>     PATTERNBLOCK, patternBlock, parsePatternBlock
>   , showPatternBlock, toPatternBlock
>   , -- match statement
>     MATCHSTMT, matchStmt, parseMatchStmt
>   , showMatchStmt
>   , toMatchStmt, CanonMatchStmt
>   , -- path
>     PATH, path, parsePath, showPath
>   , toPath, CanonPath_(..), CanonPath
>   , -- selector
>     SELECTOR, selector, parseSelector, showSelector
>   , toSelector, CanonSelector
>   , -- self
>     Self(..), notSelf 
>   , -- program block
>     PROGBLOCK, progBlock, parseProgBlock
>   , showProgBlock
>   , toProgBlock
>   , -- program statement
>     PROGSTMT, progStmt, parseProgStmt, showProgStmt
>   , toProgStmt, CanonProgStmt
>   , -- preface
>     PREFACE, preface, parsePreface, showPreface
>   , toPreface, CanonPreface(..)
>   , -- imports
>     IMPORTS, imports, parseImports, showImports
>   , -- import statement
>     IMPORTSTMT, importStmt, parseImportStmt
>   , showImportStmt
>   , -- include
>     INCLUDE, include, parseInclude, showInclude
>   , toInclude, CanonInclude(..)
>   , -- tokens
>     TOKEN, PUNCTUATION(..), TokenParser, Parser
>   , showToken, showPunctuation
>   , tokens, anyToken, whitespace, numLiteral
>   , textLiteral
>   , identifier, symbol, keyword, punctuation, eof
>   , -- identifier
>     IDENTIFIER, parseIdentifier, showIdentifier
>   , TEXTLITERAL, parseTextLiteral, showTextLiteral
>   , -- parse
>     parse
>   ) where
> import Goat.Lang.Parser.Block
> import Goat.Lang.Parser.Pattern
> import Goat.Lang.Parser.Path
> import Goat.Lang.Parser.Preface
> import Goat.Lang.Parser.Token
> import Text.Parsec (parse)