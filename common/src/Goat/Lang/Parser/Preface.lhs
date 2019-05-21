> {-# LANGUAGE TypeFamilies, FlexibleContexts #-}
> module Goat.Lang.Parser.Preface where
> import Goat.Lang.Parser.Token
> import Goat.Lang.Parser.Block
> import Goat.Lang.Parser.Pattern
> import Goat.Lang.Class
> import Data.Void (Void)
> import Text.Parsec ((<|>))

Program
-------

A *program block* is a sequence of *program statement*s,
separated and optionally terminated by semi-colons (';').
A *program statement* is left hand side *pattern*,
followed by an equals sign ('='),
followed by a right hand side *definition*.

    PROGBLOCK := [PROGSTMT [';' PROGRAM]]
    PROGSTMT := PATTERN '=' DEFINITION

Concretely

> data PROGBLOCK a =
>   PROGBLOCK_END |
>   PROGBLOCK_STMT (PROGSTMT a) (PROGBLOCK_STMT a)
> data PROGBLOCK_STMT a =
>   PROGBLOCK_STMTEND |
>   PROGBLOCK_STMTSEP (PROGBLOCK a)
> data PROGSTMT a = PROGSTMT_EQ PATTERN a

Parse with

> progBlock = (do
>   a <- progStmt
>   b <- progBlockStmt
>   return (PROGBLOCK_STMT a b)) <|>
>   return PROGBLOCK_END
>   where
>     progBlockStmt :: Parser a -> Parser (PROGBLOCK_STMT a)
>     progBlockStmt p = sepNext p <|> return PROGBLOCK_STMTEND
>       where
>         sepNext p =
>           punctuation SEP_SEMICOLON >>
>           (PROGBLOCK_STMTSEP <$> progBlock p)

> progStmt :: Parser a -> Parser (PROGSTMT a)
> progStmt p = do
>   l <- pattern
>   symbol "="
>   a <- p
>   return (PROGSTMT_EQ l a)

Interpret as syntax

> parseProgBlock
>  :: ProgBlock_ r
>  => (a -> Item (Rhs r)) -> PROGRAM (Item (Rhs r)) -> r
> parseProgBlock k p = fromList (toList p) where
>   toList PROGBLOCK_END = []
>   toList (PROGBLOCK_STMT a PROGBLOCK_STMTEND) =
>     [parseProgStmt k a]
>   toList (PROGBLOCK_STMT a (PROGBLOCK_STMTSEP b)) =
>     parseProgStmt k a : toList b

> parseProgStmt
>  :: ProgStmt_ r => (a -> Rhs r) -> PROGSTMT a -> r
> parseProgStmt k (PROGSTMT_EQ l a) =
>   parsePattern l #= k a

Show

> showProgBlock :: (a -> ShowS) -> PROGBLOCK a -> ShowS
> showProgBlock _sa PROGBLOCK_END = id
> showProgBlock sa (PROGBLOCK_STMT a b) =
>   showProgStmt sa a .
>   showProgramStmt sa b
>   where 
>     showProgramStmt
>      :: (a -> ShowS) -> PROGBLOCK_STMT a -> ShowS
>     showProgramStmt _sa PROGBLOCK_STMTEND = showChar '\n'
>     showProgramStmt sa (PROGBLOCK_STMTSEP b) =
>       showPunctuation SEP_SEMICOLON .
>       showChar '\n' .
>       showProgBlock sa b

> showProgStmt :: (a -> ShowS) -> PROGSTMT a -> ShowS 
> showProgStmt sa (PROGSTMT_EQ l a) =
>   showPattern l .
>   showSymbolSpaced "=" .
>   sa a

Convert from canonical representation

> toProgBlock :: (a -> b) -> [CanonStmt Void a] -> PROGBLOCK b
> toProgBlock _f [] = PROGBLOCK_END
> toProgBlock f (s:ss) =
>   PROGBLOCK_STMT
>     (toProgStmt f s)
>     (PROGBLOCK_STMTSEP (toProgBlock f ss))

> toProgStmt :: (a -> b) -> CanonStmt Void a -> PROGSTMT b
> toProgStmt f (p :#= a) = PROGSTMT_EQ (toPattern p) (f a)

> proofProgram :: PROGRAM -> PROGRAM
> proofProgram = toProgram . parseProgram

> proofProgBlock :: PROGBLOCK a -> PROGBLOCK a
> proofProgBlock = toProgBlock id . parseProgBlock id

> proofProgStmt :: PROGSTMT a -> PROGSTMT a
> proofProgStmt = toProgStmt id . parseProgStmt id

Preface
-------

The grammar for a *preface* is either an *imports*
or a plain *include*.
An *imports* is either a *module*
or begins with the keyword '@imports'
followed by an *imports block*,
followed by another *imports*.
An *imports block* is a sequence of *import statement*s,
separated and optionally terminated by semi-colons (';').
An *import statement* is an *identifier* followed by an equals sign
('='), followed by a *text literal*.
A *module* section begins with the keyword '@module',
followed by an *include*.
An *include* section is either a *module block*,
or begins with the keyword '@include'
followed by an *identifier*,
followed by a *module block*.

    PREFACE := IMPORTS | INCLUDE
    IMPORTS :=
      ['@imports' IMPORTSBLOCK] IMPORTS |
      '@module' INCLUDE
    IMPORTSBLOCK := [IMPORTSTMT [';' IMPORTSBLOCK]]
    IMPORTSTMT := IDENTIFIER '=' TEXTLITERAL
    INCLUDE := ['@include' IDENTIFIER] PROGRAM

Concretely

> data PREFACE =
>   PREFACE_IMPORTS (IMPORTS DEFINITION) |
>   PREFACE_INCLUDE (INCLUDE DEFINITION)
> data IMPORTS a =
>   PREFACE_EXTERNKEY IMPORTSBLOCK (IMPORTS a) |
>   PREFACE_MODULEKEY (INCLUDE a)
> data IMPORTSBLOCK =
>   IMPORTSBLOCK_END |
>   IMPORTSBLOCK_STMT IMPORTSTMT IMPORTSBLOCK_STMT
> data IMPORTSBLOCK_STMT =
>   IMPORTSBLOCK_STMTEND |
>   IMPORTSBLOCK_STMTSEP IMPORTSBLOCK
> data IMPORTSTMT = IMPORTSTMT_EQ IDENTIFIER TEXTLITERAL
> data INCLUDE a =
>   PREFACE_INCLUDEKEY IDENTIFIER (PROGBLOCK a) |
>   PREFACE_PROGBLOCK (PROGBLOCK a)

Parse with

> preface :: Preface_ r => Parser r
> preface p = externNext <|> includeNext where 
>   includeNext = parseInclude <$> include definition
>   externNext = parseImports <$> imports definition

> imports :: Parser a -> Parser (IMPORTS a)
> imports p = externKeyNext <|> moduleNext where
>   externKeyNext = do
>     keyword "extern"
>     b <- importsBody
>     i <- imports p
>     return (PREFACE_EXTERNKEY b i)
>   moduleNext =
>     keyword "module" >> (PREFACE_MODULEKEY <$> include p)
  
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
> include p = includeKeyNext <|> blockNext where
>   includeKeyNext = do 
>     keyword "include" 
>     i <- identifier
>     b <- program p
>     return (PREFACE_INCLUDEKEY i b)
>   blockNext = PREFACE_PROGBLOCK <$> program p

Convert to syntax with

> parsePreface :: Preface_ r => PREFACE -> r
> parsePreface (PREFACE_INCLUDE b) =
>   parseInclude parseDefinition b
> parsePreface (PREFACE_IMPORTS a) =
>   parseImports parseDefinition a

> parseImports
>  :: Imports_ r
>   => (a -> Rhs (Item (ModuleBody r))) -> IMPORTS a -> r
> parseImports k (PREFACE_MODULEKEY a) =
>   module_ (parseInclude k b)
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

> parseInclude
>  :: Include_ r => (a -> Rhs (Item r)) -> INCLUDE a -> r
> parseInclude k (PREFACE_PROGBLOCK m) = parseProgram k m
> parseInclude k (PREFACE_INCLUDEKEY i b) =
>   include_ (parseIdentifier i) (parseProgram k b)

and show with

> showPreface :: PREFACE -> ShowS
> showPreface (PREFACE_INCLUDE b) = showInclude showDefinition b
> showPreface (PREFACE_IMPORTS i) = showImports showDefinition i

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
> showInclude sa (PREFACE_PROGBLOCK b) = 
>   showProgram sa b
> showInclude sa (PREFACE_INCLUDEKEY i b) =
>   showKeyword "include" .
>   showChar ' ' .
>   showIdentifier i .
>   showChar '\n' .
>   showProgram sa b

> showModule :: (a -> ShowS) -> MODULE a -> ShowS
> showModule sa (PREFACE_MODULEKEY b) =
>   showKeyword "module" .
>   showChar '\n' .
>   showInclude sa b

We define syntax instances for canonical grammar types.

> data CanonInclude a =
>   Incl Ident a | Program a

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
>   type Item (INCLUDE a) = CanonStmt Void a
>   fromList bs = PREFACE_PROGBLOCK (toProgBlock id bs)
>   toList = error "IsList (INCLUDE a): toList"

> instance IsList PREFACE where
>   type Item PREFACE =
>     CanonStmt Void (CanonExpr (Either Self IDENTIFIER))
>   fromList bs =
>     PREFACE_INCLUDE (fromList (map (fmap toDefinition) bs))
>   toList = error "IsList (PREFACE a): toList"

> instance Module_ (IMPORTS a) where
>   type ModuleBody (IMPORTS a) = INCLUDE a
>   module_ b = PREFACE_MODULEKEY b

> instance Module_ PREFACE where
>   type ModuleBody PREFACE =
>     INCLUDE (CanonExpr (Either Self IDENTIFIER))
>   module_ b = PREFACE_IMPORTS (module_ b)

> instance Include_ (INCLUDE a) where
>   type Include (INCLUDE a) = IDENTIFIER
>   include_ i b = PREFACE_INCLUDEKEY i (toProgram id b)

> instance Include_ (PREFACE a) where
>   type Include (PREFACE a) = IDENTIFIER
>   include_ i b = PREFACE_INCLUDE (include_ i b)

> instance Extern_ (IMPORTS a) where
>   type ImportItem (IMPORTS a) = IMPORTSTMT
>   type Intern (IMPORTS a) = IMPORTS a
>   extern_ bs a = PREFACE_EXTERNKEY (fromList bs) a

> instance Extern_ PREFACE where
>   type ImportItem PREFACE = IMPORTSTMT
>   type Intern PREFACE = IMPORTS a
>   extern_ bs a = PREFACE_IMPORTS (extern_ bs a)
