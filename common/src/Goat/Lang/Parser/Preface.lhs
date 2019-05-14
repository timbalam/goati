> {-# LANGUAGE TypeFamilies, FlexibleContexts #-}
> module Goat.Lang.Parser.Preface where
> import Goat.Lang.Parser.Token
> import Goat.Lang.Parser.Block
> import Goat.Lang.Class
> import Text.Parsec ((<|>))

Preface
-------

The grammar for a *preface* is either an *imports*
or a plain *include*.
An *imports* is either a *module*
or begins with the keyword '@imports'
followed by an *import body*,
followed by another *imports*.
An *import body* is a sequence of *import statement*s,
separated and optionally terminated by semi-colons (';').
An *import statement* is an *identifier* followed by an equals sign
('='), followed by a *text literal*.
A *module* section begins with the keyword '@module',
followed by an *include*.
An *include* section is either a *block*,
or begins with the keyword '@include'
followed by an *identifier*,
followed by a *block*.

    PREFACE := IMPORTS | INCLUDE
    IMPORTS := ['@imports' IMPORTSBLOCK] IMPORTS | MODULE
    IMPORTSBLOCK := [IMPORTSTMT [';' IMPORTSBLOCK]]
    IMPORTSTMT := IDENTIFIER '=' TEXTLITERAL
    INCLUDE := ['@include' IDENTIFIER] BLOCK
    MODULE := '@module' INCLUDE

Concretely

> data PREFACE a =
>   PREFACE_IMPORTS (IMPORTS a) |
>   PREFACE_INCLUDE (INCLUDE a)
> data IMPORTS a =
>   PREFACE_EXTERNKEY IMPORTSBLOCK (IMPORTS a) |
>   PREFACE_MODULE (MODULE a)
> data IMPORTSBLOCK =
>   IMPORTSBLOCK_END |
>   IMPORTSBLOCK_STMT IMPORTSTMT IMPORTSBLOCK_STMT
> data IMPORTSBLOCK_STMT =
>   IMPORTSBLOCK_STMTEND |
>   IMPORTSBLOCK_STMTSEP IMPORTSBLOCK
> data IMPORTSTMT = IMPORTSTMT_EQ IDENTIFIER TEXTLITERAL
> newtype MODULE a = PREFACE_MODULEKEY (INCLUDE a)
> data INCLUDE a =
>   PREFACE_INCLUDEKEY IDENTIFIER (BLOCK a) |
>   PREFACE_BLOCK (BLOCK a)

Parse with

> preface :: Parser a -> Parser (PREFACE a)
> preface p = externNext <|> includeNext where 
>   includeNext = PREFACE_INCLUDE <$> include p
>   externNext = PREFACE_IMPORTS <$> imports p

> imports :: Parser a -> Parser (IMPORTS a)
> imports p = externKeyNext <|> moduleNext where
>   externKeyNext = do
>     keyword "extern"
>     b <- importsBody
>     i <- imports p
>     return (PREFACE_EXTERNKEY b i)
>   moduleNext = PREFACE_MODULE <$> module' p
  
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

> module' :: Parser a -> Parser (MODULE a)
> module' p =
>   keyword "module" >> (PREFACE_MODULEKEY <$> include p)

> include :: Parser a -> Parser (INCLUDE a)
> include p = includeKeyNext <|> blockNext where
>   includeKeyNext = do 
>     keyword "include" 
>     i <- identifier
>     b <- block p
>     return (PREFACE_INCLUDEKEY i b)
>   blockNext = PREFACE_BLOCK <$> block p

Convert to syntax with

> parsePreface
>  :: Preface_ r => (a -> Rhs (Item r)) -> PREFACE a -> r
> parsePreface k (PREFACE_INCLUDE b) = parseInclude k b
> parsePreface k (PREFACE_IMPORTS a) = parseImports k a

> parseImports
>  :: Imports_ r
>   => (a -> Rhs (Item (ModuleBody r))) -> IMPORTS a -> r
> parseImports k (PREFACE_MODULE a) = parseModule k a
> parseImports k (PREFACE_EXTERNKEY b a) =
>   extern_ (toList b) (parseImports k a)
>   where
>     toList IMPORTSBLOCK_END = []
>     toList (IMPORTSBLOCK_STMT a IMPORTSBLOCK_STMTEND) =
>       [parseImportStmt a]
>     toList (IMPORTSBLOCK_STMT a (IMPORTSBLOCK_STMTSEP b)) =
>       parseImportStmt a : toList b

> parseImportStmt :: ImportStmt_ s => IMPORTSTMT -> s
> parseImportStmt (IMPORTSTMT_EQ a b) =
>   parseIdentifier a #= parseTextLiteral b

> parseModule
>  :: Module_ r
>  => (a -> Rhs (Item (ModuleBody r))) -> MODULE a -> r
> parseModule k (PREFACE_MODULEKEY b) = module_ (parseInclude k b)

> parseInclude
>  :: Include_ r => (a -> Rhs (Item r)) -> INCLUDE a -> r
> parseInclude k (PREFACE_BLOCK m) = parseBlock k m
> parseInclude k (PREFACE_INCLUDEKEY i b) =
>   include_ (parseIdentifier i) (parseBlock k b)

and show with

> showPreface :: (a -> ShowS) -> PREFACE a -> ShowS
> showPreface sa (PREFACE_INCLUDE b) = showInclude sa b
> showPreface sa (PREFACE_IMPORTS i) = showImports sa i

> showImports :: (a -> ShowS) -> IMPORTS a -> ShowS
> showImports sa (PREFACE_MODULE a) = showModule sa a
> showImports sa (PREFACE_EXTERNKEY bs i) =
>   showKeyword "extern" .
>   showChar '\n' .
>   showImportsBody (showChar '\n') bs .
>   showImports sa i
>   where
>     showImportsBody :: ShowS -> IMPORTSBLOCK -> ShowS
>     showImportsBody _wsep IMPORTSBLOCK_END = id
>     showImportsBody wsep (IMPORTSBLOCK_STMT a b) =
>       showImportStmt a .
>       showImportsBodyStmt wsep b
>     
>     showImportsBodyStmt :: ShowS -> IMPORTSBLOCK_STMT -> ShowS
>     showImportsBodyStmt wsep IMPORTSBLOCK_STMTEND = wsep
>     showImportsBodyStmt wsep (IMPORTSBLOCK_STMTSEP b) =
>       showPunctuation SEP_SEMICOLON .
>       wsep .
>       showImportsBody wsep b

> showImportStmt :: IMPORTSTMT -> ShowS
> showImportStmt (IMPORTSTMT_EQ i t) =
>   showIdentifier i .
>   showSymbolSpaced "=" .
>   showTextLiteral t

> showInclude :: (a -> ShowS) -> INCLUDE a -> ShowS
> showInclude sa (PREFACE_BLOCK b) = 
>   showBlock (showChar '\n') sa b
> showInclude sa (PREFACE_INCLUDEKEY i b) =
>   showKeyword "include" .
>   showChar ' ' .
>   showIdentifier i .
>   showChar '\n' .
>   showBlock (showChar '\n') sa b

> showModule :: (a -> ShowS) -> MODULE a -> ShowS
> showModule sa (PREFACE_MODULEKEY b) =
>   showKeyword "module" .
>   showChar '\n' .
>   showInclude sa b

We define syntax instances for the grammar types directly.

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

> instance IsList (INCLUDE a) where
>   type Item (INCLUDE a) = CanonStmt a
>   fromList bs = PREFACE_BLOCK (toBlock id bs)
>   toList = error "IsList (INCLUDE a): toList"

> instance IsList (PREFACE a) where
>   type Item (PREFACE a) = CanonStmt a
>   fromList bs = PREFACE_INCLUDE (fromList bs)
>   toList = error "IsList (PREFACE a): toList"

> instance Module_ (MODULE a) where
>   type ModuleBody (MODULE a) = INCLUDE a
>   module_ b = PREFACE_MODULEKEY b

> instance Module_ (IMPORTS a) where
>   type ModuleBody (IMPORTS a) = INCLUDE a
>   module_ b = PREFACE_MODULE (module_ b)

> instance Module_ (PREFACE a) where
>   type ModuleBody (PREFACE a) = INCLUDE a
>   module_ b = PREFACE_IMPORTS (module_ b)

> instance Include_ (INCLUDE a) where
>   type IncludeKey (INCLUDE a) = IDENTIFIER
>   type Includes (INCLUDE a) = [CanonStmt a]
>   include_ i b = PREFACE_INCLUDEKEY i (toBlock id b)

> instance Include_ (PREFACE a) where
>   type IncludeKey (PREFACE a) = IDENTIFIER
>   type Includes (PREFACE a) = [CanonStmt a]
>   include_ i b = PREFACE_INCLUDE (include_ i b)

> instance Extern_ (IMPORTS a) where
>   type ImportItem (IMPORTS a) = IMPORTSTMT
>   type Externs (IMPORTS a) = IMPORTS a
>   extern_ bs a = PREFACE_EXTERNKEY (fromList bs) a

> instance Extern_ (PREFACE a) where
>   type ImportItem (PREFACE a) = IMPORTSTMT
>   type Externs (PREFACE a) = IMPORTS a
>   extern_ bs a = PREFACE_IMPORTS (extern_ bs a)
