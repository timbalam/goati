> {-# LANGUAGE TypeFamilies, FlexibleContexts, FlexibleInstances, TypeSynonymInstances, DeriveFunctor #-}
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

> progBlock :: Parser a -> Parser (PROGBLOCK a)
> progBlock p = (do
>   a <- progStmt p
>   b <- progBlockStmt p
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
>  => (a -> Rhs (Item r)) -> PROGBLOCK a -> r
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
    INCLUDE := ['@include' IDENTIFIER] PROGBLOCK

Concretely

> data PREFACE =
>   PREFACE_IMPORTS (IMPORTS INCLUDE) |
>   PREFACE_INCLUDE INCLUDE
> data IMPORTS a =
>   PREFACE_EXTERNKEY IMPORTSBLOCK (IMPORTS a) |
>   PREFACE_MODULEKEY a
>   deriving Functor
> data IMPORTSBLOCK =
>   IMPORTSBLOCK_END |
>   IMPORTSBLOCK_STMT IMPORTSTMT IMPORTSBLOCK_STMT
> data IMPORTSBLOCK_STMT =
>   IMPORTSBLOCK_STMTEND |
>   IMPORTSBLOCK_STMTSEP IMPORTSBLOCK
> data IMPORTSTMT = IMPORTSTMT_EQ IDENTIFIER TEXTLITERAL
> data INCLUDE =
>   PREFACE_INCLUDEKEY IDENTIFIER (PROGBLOCK DEFINITION) |
>   PREFACE_PROGBLOCK (PROGBLOCK DEFINITION)

Parse with

> preface :: Preface_ r => Parser r
> preface = externNext <|> includeNext where
>   includeNext = include
>   
>   -- externNext :: Preface_ r => Parser r
>   externNext = parseImports id <$> imports include

> imports :: Parser a -> Parser (IMPORTS a)
> imports p = externKeyNext <|> moduleNext where
>   externKeyNext = do
>     keyword "extern"
>     b <- importsBody
>     i <- imports p
>     return (PREFACE_EXTERNKEY b i)
>   moduleNext =
>     keyword "module" >> (PREFACE_MODULEKEY <$> p)
  
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

> include :: Include_ r => Parser r
> include = includeKeyNext <|> blockNext where
>   includeKeyNext = do 
>     keyword "include" 
>     i <- identifier
>     b <- progBlock definition
>     return (include_ (parseIdentifier i) (parseProgBlock id b))
>   blockNext = parseProgBlock id <$> progBlock definition

Convert to syntax with

> parsePreface :: Preface_ r => PREFACE -> r
> parsePreface (PREFACE_INCLUDE b) = parseInclude b
> parsePreface (PREFACE_IMPORTS a) = parseImports parseInclude a

> parseImports
>  :: Imports_ r
>   => (a -> ModuleBody r) -> IMPORTS a -> r
> parseImports k (PREFACE_MODULEKEY a) = module_ (k a)
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
>  :: Include_ r => INCLUDE -> r
> parseInclude (PREFACE_PROGBLOCK m) =
>   parseProgBlock parseDefinition m
> parseInclude (PREFACE_INCLUDEKEY i b) =
>   include_ (parseIdentifier i)
>    (parseProgBlock parseDefinition b)

and show with

> showPreface :: PREFACE -> ShowS
> showPreface (PREFACE_INCLUDE b) = showInclude b
> showPreface (PREFACE_IMPORTS i) = showImports showInclude i

> showImports :: (a -> ShowS) -> IMPORTS a -> ShowS
> showImports sa (PREFACE_MODULEKEY a) =
>   showKeyword "module" .
>   showChar '\n' .
>   sa a
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

> showInclude :: INCLUDE -> ShowS
> showInclude (PREFACE_PROGBLOCK b) = 
>   showProgBlock showDefinition b
> showInclude (PREFACE_INCLUDEKEY i b) =
>   showKeyword "include" .
>   showChar ' ' .
>   showIdentifier i .
>   showChar '\n' .
>   showProgBlock showDefinition b

We define syntax instances for canonical grammar types,
and translations to our grammar types.

> type CanonPreface =
>   Either CanonInclude (IMPORTS CanonInclude)

> proofPreface :: PREFACE -> CanonPreface
> proofPreface = parsePreface

> data CanonInclude =
>   Include IDENTIFIER [CanonStmt Void (CanonExpr IDENTIFIER)] |
>   Program [CanonStmt Void (CanonExpr IDENTIFIER)]

> proofInclude :: INCLUDE -> CanonInclude
> proofInclude = parseInclude

> proofImports :: IMPORTS a -> IMPORTS a
> proofImports = parseImports id

> proofImportStmt :: IMPORTSTMT -> IMPORTSTMT
> proofImportStmt = parseImportStmt

> toPreface
>  :: CanonPreface -> PREFACE
> toPreface (Left inc) = PREFACE_INCLUDE (toInclude inc)
> toPreface (Right imp) = PREFACE_IMPORTS (toInclude <$> imp)

> toInclude 
>  :: CanonInclude -> INCLUDE
> toInclude (Include n ss) =
>   PREFACE_INCLUDEKEY n (toProgBlock toDefinition ss)
> toInclude (Program ss) =
>   PREFACE_PROGBLOCK (toProgBlock toDefinition ss)

Instances

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

> instance IsList CanonInclude where
>   type Item CanonInclude =
>     CanonStmt Void (CanonExpr (Either Self IDENTIFIER))
>   fromList bs = Program (map (fmap unself) bs)
>   toList = error "IsList CanonInclude: toList"

> instance IsList CanonPreface where
>   type Item CanonPreface =
>     CanonStmt Void (CanonExpr (Either Self IDENTIFIER))
>   fromList bs = Left (fromList bs)
>   toList = error "IsList CanonPreface: toList"

> instance Include_ CanonInclude where
>   type Name CanonInclude = IDENTIFIER
>   include_ i bs = Include i (map (fmap unself) bs)

> instance Include_ CanonPreface where
>   type Name CanonPreface = IDENTIFIER
>   include_ i b = Left (include_ i b)

> instance Extern_ (IMPORTS a) where
>   type ImportItem (IMPORTS a) = IMPORTSTMT
>   type Intern (IMPORTS a) = IMPORTS a
>   type ModuleBody (IMPORTS a) = a
>   extern_ bs imp = PREFACE_EXTERNKEY (fromList bs) imp
>   module_ a = PREFACE_MODULEKEY a

> instance Extern_ CanonPreface where
>   type ImportItem CanonPreface = IMPORTSTMT
>   type Intern CanonPreface = IMPORTS CanonInclude
>   type ModuleBody CanonPreface = CanonInclude
>   extern_ bs imp = Right (extern_ bs imp)
>   module_ a = Left a
