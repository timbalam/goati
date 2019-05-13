> {-# LANGUAGE TypeFamilies, FlexibleContexts #-}
> module Goat.Lang.Parser.Preface where
> import Goat.Lang.Parser.Token
> import Goat.Lang.Parser.Block
> import Goat.Lang.Class
> import Text.Parsec ((<|>))

Preface
-------

The grammar for a *preface* is either an *import*
or a plain *block*.
An *import* section optionally begins with the keyword '@extern'
followed by an *import body*,
and ends with an *include* section.
An *import body* is a sequence of *import statement*s,
separated and optionally terminated by semi-colons (';').
An *import statement* is an *identifier* followed by an equals sign
('='), followed by a *text literal*.
An *include* section optionally begins with the keyword '@include' followed by an *identifier*,
and ends with a *module* section.
A *module* section begins with the keyword '@module',
followed by a *block*.

    PREFACE := IMPORTS | BLOCK
    IMPORTS := ['@extern' IMPORTSBLOCK] INCLUDE
    IMPORTSBLOCK := [IMPORTSTMT [';' IMPORTSBLOCK]]
    IMPORTSTMT := IDENTIFIER '=' TEXTLITERAL
    INCLUDE := ['@include' IDENTIFIER] MODULE
    MODULE := '@module' BLOCK

Concretely

> data PREFACE a =
>   PREFACE_IMPORTS (IMPORTS a) |
>   PREFACE_BLOCK (BLOCK a)
> data IMPORTS a =
>   PREFACE_EXTERNKEY IMPORTSBLOCK (INCLUDE a) |
>   PREFACE_INCLUDE (INCLUDE a)
> data IMPORTSBLOCK =
>   IMPORTSBLOCK_END |
>   IMPORTSBLOCK_STMT IMPORTSTMT IMPORTSBLOCK_STMT
> data IMPORTSBLOCK_STMT =
>   IMPORTSBLOCK_STMTEND |
>   IMPORTSBLOCK_STMTSEP IMPORTSBLOCK
> data IMPORTSTMT = IMPORTSTMT_EQ IDENTIFIER TEXTLITERAL
> data INCLUDE a =
>   PREFACE_INCLUDEKEY IDENTIFIER (MODULE a) |
>   PREFACE_MODULE (MODULE a)
> newtype MODULE a = PREFACE_MODULEKEY (BLOCK a)

> proofPreface :: PREFACE a -> PREFACE a
> proofPreface = parsePreface id

> proofImports :: IMPORTS a -> IMPORTS a
> proofImports = parseImports id

> proofImportStmt :: IMPORTSTMT -> IMPORTSTMT
> proofImportStmt = parseImportStmt

> proofInclude :: INCLUDE a -> INCLUDE a
> proofInclude = parseInclude id

> proofModule :: MODULE a -> MODULE a
> proofModule = parseModule id

Parse with

> preface :: Parser a -> Parser (PREFACE a)
> preface p = importNext <|> blockNext where 
>   blockNext = PREFACE_BLOCK <$> block p
>   importNext = PREFACE_IMPORTS <$> imports p

> imports :: Parser a -> Parser (IMPORTS a)
> imports p = externNext <|> includeNext where
>   externNext = do
>     keyword "extern"
>     b <- importsBody
>     i <- include p
>     return (PREFACE_EXTERNKEY b i)
>   includeNext = PREFACE_INCLUDE <$> include p
  
> importsBody :: Parser IMPORTSBLOCK
> importsBody = (do
>   a <- importStmt
>   b <- importsBodyStmt
>   return (IMPORTSBLOCK_STMT a b)) <|>
>   return IMPORTSBLOCK_END
>   where
>     importsBodyStmt :: Parser IMPORTSBLOCK_STMT
>     importsBodyStmt = (do
>       punctuation SEP_SEMICOLON
>       b <- importsBody
>       return (IMPORTSBLOCK_STMTSEP b)) <|>
>       return IMPORTSBLOCK_STMTEND

> importStmt :: Parser IMPORTSTMT
> importStmt = do
>   a <- identifier
>   symbol "="
>   b <- textLiteral
>   return (IMPORTSTMT_EQ a b)

> include :: Parser a -> Parser (INCLUDE a)
> include p = includeNext <|> moduleNext where
>   includeNext = do 
>     keyword "include" 
>     i <- identifier
>     m <- module' p
>     return (PREFACE_INCLUDEKEY i m)
>   moduleNext = PREFACE_MODULE <$> module' p

> module' :: Parser a -> Parser (MODULE a)
> module' p = keyword "module" >> (PREFACE_MODULEKEY <$> block p)

Convert to syntax with

> parsePreface
>  :: Preface_ r => (a -> Rhs (Item r)) -> PREFACE a -> r
> parsePreface k (PREFACE_BLOCK b) = parseBlock k b
> parsePreface k (PREFACE_IMPORTS a) = parseImports k a

> parseImports
>  :: Imports_ r
>   => (a -> Rhs (Item (ModuleBody r))) -> IMPORTS a -> r
> parseImports k (PREFACE_INCLUDE a) = parseInclude k a
> parseImports k (PREFACE_EXTERNKEY b a) =
>   extern_ (toList b) (parseInclude k a)
>   where
>     toList IMPORTSBLOCK_END = []
>     toList (IMPORTSBLOCK_STMT a IMPORTSBLOCK_STMTEND) =
>       [parseImportStmt a]
>     toList (IMPORTSBLOCK_STMT a (IMPORTSBLOCK_STMTSEP b)) =
>       parseImportStmt a : toList b

> parseImportStmt :: ImportStmt_ s => IMPORTSTMT -> s
> parseImportStmt (IMPORTSTMT_EQ a b) =
>   parseIdentifier a #= parseTextLiteral b

> parseInclude
>  :: Include_ r
>  => (a -> Rhs (Item (ModuleBody r))) -> INCLUDE a -> r
> parseInclude k (PREFACE_MODULE m) = parseModule k m
> parseInclude k (PREFACE_INCLUDEKEY i m) =
>   include_ (parseIdentifier i) (parseModule k m)

> parseModule
>  :: Module_ r
>  => (a -> Rhs (Item (ModuleBody r))) -> MODULE a -> r
> parseModule k (PREFACE_MODULEKEY b) = module_ (parseBlock k b)

and show with

> showPreface :: (a -> ShowS) -> PREFACE a -> ShowS
> showPreface sa (PREFACE_BLOCK b) =
>   showBlock (showChar '\n') sa b
> showPreface sa (PREFACE_IMPORTS i) = showImports sa i

> showImports :: (a -> ShowS) -> IMPORTS a -> ShowS
> showImports sa (PREFACE_INCLUDE a) = showInclude sa a
> showImports sa (PREFACE_EXTERNKEY bs a) =
>   showKeyword (KEYWORD_ATSIGN (IDENTIFIER "extern")) .
>   showImportsBody (showChar '\n') bs .
>   showInclude sa a
>   where
>     showImportsBody :: ShowS -> IMPORTSBLOCK -> ShowS
>     showImportsBody wsep IMPORTSBLOCK_END = wsep
>     showImportsBody wsep (IMPORTSBLOCK_STMT a b) =
>       wsep .
>       showImportStmt a .
>       showImportsBodyStmt wsep b
>     
>     showImportsBodyStmt :: ShowS -> IMPORTSBLOCK_STMT -> ShowS
>     showImportsBodyStmt _wsep IMPORTSBLOCK_STMTEND = id
>     showImportsBodyStmt wsep (IMPORTSBLOCK_STMTSEP b) =
>       showPunctuation SEP_SEMICOLON .
>       showImportsBody wsep b

> showImportStmt :: IMPORTSTMT -> ShowS
> showImportStmt (IMPORTSTMT_EQ i t) =
>   showIdentifier i .
>   showSymbolSpaced (SYMBOL "=") .
>   showTextLiteral t

> showInclude :: (a -> ShowS) -> INCLUDE a -> ShowS
> showInclude sa (PREFACE_MODULE m) = showModule sa m
> showInclude sa (PREFACE_INCLUDEKEY i m) =
>   showKeyword (KEYWORD_ATSIGN (IDENTIFIER "include")) .
>   showChar ' ' .
>   showIdentifier i .
>   showChar '\n' .
>   showModule sa m

> showModule :: (a -> ShowS) -> MODULE a -> ShowS
> showModule sa (PREFACE_MODULEKEY b) =
>   showKeyword (KEYWORD_ATSIGN (IDENTIFIER "module")) .
>   showBlock (showChar '\n') sa b

Syntax class instances

> instance Assign_ IMPORTSTMT where
>   type Lhs IMPORTSTMT = IDENTIFIER
>   type Rhs IMPORTSTMT = TEXTLITERAL
>   (#=) = IMPORTSTMT_EQ

> instance IsList IMPORTSBLOCK where
>   type Item IMPORTSBLOCK = IMPORTSTMT
>   fromList [] = IMPORTSBLOCK_END
>   fromList (s:ss) =
>     IMPORTSBLOCK_STMT s (IMPORTSBLOCK_STMTSEP (fromList ss)) 
>   toList = error "IsList IMPORTSBLOCK: toList"

> instance IsList (PREFACE a) where
>   type Item (PREFACE a) = STMT a
>   fromList bs = PREFACE_BLOCK (fromList bs)
>   toList = error "IsList (PREFACE a): toList"

> instance Module_ (MODULE a) where
>   type ModuleBody (MODULE a) = BLOCK a
>   module_ b = PREFACE_MODULEKEY b

> instance Module_ (INCLUDE a) where
>   type ModuleBody (INCLUDE a) = BLOCK a
>   module_ b = PREFACE_MODULE (module_ b)

> instance Module_ (IMPORTS a) where
>   type ModuleBody (IMPORTS a) = BLOCK a
>   module_ b = PREFACE_INCLUDE (module_ b)

> instance Module_ (PREFACE a) where
>   type ModuleBody (PREFACE a) = BLOCK a
>   module_ b = PREFACE_IMPORTS (module_ b)

> instance Include_ (INCLUDE a) where
>   type IncludeKey (INCLUDE a) = IDENTIFIER
>   type Includes (INCLUDE a) = MODULE a
>   include_ i m = PREFACE_INCLUDEKEY i m

> instance Include_ (IMPORTS a) where
>   type IncludeKey (IMPORTS a) = IDENTIFIER
>   type Includes (IMPORTS a) = MODULE a
>   include_ i m = PREFACE_INCLUDE (include_ i m)

> instance Include_ (PREFACE a) where
>   type IncludeKey (PREFACE a) = IDENTIFIER
>   type Includes (PREFACE a) = MODULE a
>   include_ i m = PREFACE_IMPORTS (include_ i m)

> instance Imports_ (IMPORTS a) where
>   type ImportItem (IMPORTS a) = IMPORTSTMT
>   type Imports (IMPORTS a) = INCLUDE a
>   extern_ bs a = PREFACE_EXTERNKEY (fromList bs) a

> instance Imports_ (PREFACE a) where
>   type ImportItem (PREFACE a) = IMPORTSTMT
>   type Imports (PREFACE a) = INCLUDE a
>   extern_ bs a = PREFACE_IMPORTS (extern_ bs a)
