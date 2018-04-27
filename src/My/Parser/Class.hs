{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts, RankNTypes, MultiParamTypeClasses #-}

-- | Parsers for my syntax types

module My.Parser.Class
  ( decfloat
  , binary
  , octal
  , hexidecimal
  , number
  , string
  , path
  , pathexpr
  , Parser, parse
  , ShowMy(..)
  , ReadMy(..)
  )
  where
  
import qualified My.Types.Parser.Class as C
import My.Types.Parser.Class
  ( LitExpr
  , OpExpr
  , VarExpr
  , SubExpr
  , GroupExpr
  , Path
  , Rec
  , Tup
  , Patt
  , Program
  )
import My.Types.Parser
  ( Ident(..)
  , Key(..)
  , Vis(..)
  , Res(..)
  , Import(..)
  , Name
  , Unop(..)
  , Binop(..)
  )
import My.Parser
  ( ShowMy(..)
  , ReadMy(..)
  , comment, spaces, point, stringfragment, escapedchars, identpath
  , eqsep, semicolonsep, ellipsissep, commasep
  , braces, parens, staples
  , readOr, readAnd, readEq, readNe, readLt, readGt, readLe
  , readGe, readAdd, readSub, readProd, readDiv, readPow
  , readNeg, readNot
  )
import qualified Data.Text as T
import qualified Text.Parsec as P
import Text.Parsec ((<|>), (<?>), try, parse)
import Text.Parsec.Text  (Parser)
import Numeric (readHex, readOct)
import Control.Applicative (liftA2)
import Data.Char (showLitChar)
import Data.Foldable (foldl', concat, toList)
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import Data.Semigroup ((<>), option)
import Data.Function ((&))
import Data.Bifunctor (bimap)
import Control.Monad.State
     
    
-- | Parse any valid numeric literal
number :: C.LitExpr r => Parser r
number =
  (binary
    <|> octal
    <|> hexidecimal
    <|> decfloat
    <?> "number literal")
    <* spaces
    
    
-- | Parse a valid binary number
binary :: C.LitExpr r => Parser r
binary =
  do
    try (P.string "0b")
    C.integerLit . bin2dig <$> integer (P.oneOf "01")
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parse a valid octal number
octal :: C.LitExpr r => Parser r
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . C.integerLit . oct2dig
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parse a valid hexidecimal number
hexidecimal :: C.LitExpr r => Parser r
hexidecimal =
  try (P.string "0x") >> integer P.hexDigit >>= return . C.integerLit . hex2dig
  where 
    hex2dig x =
      fst (readHex x !! 0)
  
  
  
-- | Parse a sequence of underscore spaced digits
integer :: Parser Char -> Parser String
integer d =
  (P.sepBy1 d . P.optional) (P.char '_')
   
    
-- | Parser for valid decimal or floating point number
decfloat :: C.LitExpr r => Parser r
decfloat =
  prefixed
    <|> unprefixed
  where
    prefixed =
      do
        try (P.string "0d")
        C.integerLit . read <$> integer P.digit
        
    unprefixed =
      do
        xs <- integer P.digit
        fracnext xs                               -- int frac
                                                  -- int frac exp
          <|> expnext xs                          -- int exp
          <|> (return . C.integerLit) (read xs)   -- int
          
    fracnext xs =
      do 
        y <- point
        m <- P.optionMaybe (integer P.digit)
        case m of
          Nothing ->
            -- frac
            (return . C.numberLit . read) (xs ++ [y, '0'])
            
          Just ys ->
            expnext (xs ++ [y] ++ ys)   -- frac exp
              <|>
                (return . C.numberLit . read) (xs ++ [y] ++ ys)
                                      -- frac
          
    expnext xs =
      do 
        e <- P.oneOf "eE"
        sgn <- P.option [] (P.oneOf "+-" >>= return . pure)
        ys <- integer P.digit
        (return . C.numberLit . read) (xs ++ e:sgn ++ ys)


-- | Parse a double-quote wrapped string literal
string :: C.LitExpr r => Parser r
string =
  C.stringLit . T.pack <$> stringfragment <?> "string literal"

  

-- | Parse a relative path
path :: C.Path m => a -> Parser (m a)
path = rest . pure
  where
    rest x =
      (readsMy >>= rest . C.at x)
        <|> return x
        
instance (ReadMy a, C.Path m) => ReadMy (m a) where
  readsMy = path . readsMy


syntax :: C.Syntax r g (Name Ident Key Import) => Parser r
syntax =
    orexpr    -- '!' ...
              -- '-' ...
              -- '"' ...
              -- '(' ...
              -- digit ...
              -- '{' ...
              -- '.' alpha ...
              -- alpha ...
              -- '@' ...
      <?> "expression"
                    
          
-- | Parse an expression observing operator precedence
orexpr :: C.Syntax r g (Name Ident Key Import) => Parser r
orexpr =
  P.chainl1 andexpr (C.binop <$> readOr)

      
andexpr :: C.Syntax r g (Name Ident Key Import) => Parser r
andexpr =
  P.chainl1 cmpexpr (C.binop <$> readAnd)

        
cmpexpr :: C.Syntax r g (Name Ident Key Import) => Parser r
cmpexpr =
  do
    a <- addexpr
    (do
       s <- op
       b <- addexpr
       return (s a b))
      <|> return a
  where
    op = C.binop <$> (readGt <|> readLt <|> readEq <|> readNe <|> readGe <|> readLe)
   
   
addexpr :: C.Syntax r g (Name Ident Key Import) => Parser r
addexpr =
  P.chainl1 mulexpr (C.binop <$> (readAdd <|> readSub))


mulexpr :: C.Syntax r g (Name Ident Key Import) => Parser r
mulexpr =
  P.chainl1 powexpr (C.binop <$> (readProd <|> readDiv))


powexpr :: C.Syntax r g (Name Ident Key Import) => Parser r
powexpr =
  P.chainl1 term (C.binop <$> readPow)
    where
      term =
        unop            -- '!'
                        -- '-'
          <|> pathexpr  -- '"'
                        -- '('
                        -- digit
                        -- '{'
                        -- '.'
                        -- alpha
          
-- | Parse an unary operation
unop :: C.Syntax r g (Name Ident Key Import) => Parser r
unop = C.unop <$> readsMy <*> pathexpr
        
        
-- | Parse a chain of field accesses and extensions
pathexpr :: C.Syntax r g (Name Ident Key Import) => Parser r
pathexpr =
  first >>= rest
  where
    next x =
      (C.extend x <$> group)
        <|> (C.at x <$> syntax)
    
    
    rest x =
      (next x >>= rest)
        <|> return x
    
    
    first =
      string                      -- '"' ...
        <|> parens disambigTuple  -- '(' ...
        <|> (C.group <$> block)   -- '{' ...
        <|> number                -- digit ...
        <|> (C.var <$> readsMy)   -- '.' alpha ...
                                  -- alpha ...
                                  -- '@' ...
        <?> "value"
        
            
    -- | Handle a tricky parsing ambiguity between plain brackets and
    --   a singleton tuple, by requiring a trailing comma for the first
    --   statement of a tuple.
    --
    --   When an opening paren is encountered, we parse a rhs expression, and 
    --   check to see if the result can be interpreted as the beginning of a 
    --   tuple statement - only if the expression is a varpath - then we 
    --   disambiguate by looking next for an assignment `=` or a comma `,` 
    --   indicating a tuple expression. Otherwise we return rhs expression
    --   (and the calling function will then expect a closing paren).
    disambigTuple :: C.Syntax r g (Name Ident Key Import) => Parser r
    disambigTuple = (syntax >>= \ (TryStmt e) -> case e of 
      Nothing -> syntax
      Just (Pub p) ->
        eqNext p                -- '=' ...
          <|> sepNext (Pub p)   -- ',' ...
          <|> syntax            -- ')' ...
      Just (Priv p) ->
        sepNext (Priv p)        -- ',' ...
          <|> syntax)           -- ')' ...
        <|> return (C.group mempty)
      where
        eqNext
          :: C.Syntax r g (Name Ident Key Import)
          => (forall p. Path p => p Key)
          -> Parser r
        eqNext p = liftA2 go (eqsep >> readsMy) tuple1 where
          go x xs = C.group (C.let_ p x <> xs)
          
        sepNext
          :: C.Syntax r g (Name Ident Key Import)
          => (forall p. Path p => Vis (p Ident) (p Key))
          -> Parser r
        sepNext p = C.group . (C.pun p <>) <$> tuple1
  
  
-- | Try to interpret an expression as the start of a tuple
--   statement
newtype TryStmt p = TryStmt (Maybe (Vis (p Ident) (p Key)))

instance C.LitExpr (TryStmt p) where
  integerLit = TryStmt Nothing
  stringLit = TryStmt Nothing
  numberLit = TryStmt Nothing
  
instance C.OpExpr (TryStmt p) where
  unop _ _ = Nothing
  binop _ _ _ = Nothing
  
instance C.Path p => C.SubExpr (TryStmt p) where
  get (TryStmt m) x = TryStmt (bimap (`C.at` x) (`C.at` x) m)
  
instance C.Path p => C.VarExpr (TryStmt p) (Name Ident Key Import) where
  var x = case x of
    Ex _ -> Nothing
    In v -> Just (bimap pure pure v)
    
instance C.GroupExpr (TryStmt p) () where
  group _ = Nothing
  extend _ _ = Nothing

        
-- | Parse a block expression
group :: C.Syntax r g a => Parser g
group = block syntax <|> tuple syntax
    
        
-- | Parse either an expression wrapped in parens or a tuple form block
tuple :: (Tup g a, Monoid g) => Parser a -> Parser g
tuple reads = parens (some <|> return mempty) <?> "tuple"
  where
    some = liftA2 (<>) (tupstmt reads) (tuple1 reads)
    
    
tuple1 :: (Tup g a, Monoid g) => Parser a -> Parser g
tuple1 reads = commasep >> msepEndBy (tupstmt reads) commasep


msepEndBy :: Monoid a => Parser a -> Parser b -> Parser a
msepEndBy p sep = msepEndBy p sep <|> return mempty

msepEndBy1 :: Monoid a => Parser a -> Parser b -> Parser a
msepEndBy1 p sep =
  do
    x <- p
    (do
      sep
      xs <- msepEndBy p sep
      return (x <> xs))
      <|> return x
      
    
block :: (Rec g a, Monoid g) => Parser a -> Parser g
block reads = braces (msepEndBy (recstmt reads) semicolonsep) <?> "block"


-- | Parse a statement of a block expression
recstmt :: (ReadMy a, Rec g a) => Parser g
recstmt = 
    letrecstmt        -- '.' alpha ...
                            -- alpha ...
      <|> destructurestmt   -- '(' ...
      <?> "statement"

    
tupstmt :: Tup g a => Parser a -> Parser g
tupstmt reads = do
    v <- readsMy
    case v of
      Priv _ -> return (C.pun v)          -- alpha ...
      Pub p ->                          -- '.' alpha ...
        (C.let_ p <$> (eqsep >> reads))
          <|> return (C.pun v)


-- | Parse a recursive let statement
letrecstmt :: Rec g a => Parser a -> Parser g
letrecstmt reads =
  do
    v <- readsMy
    case v of
      Pub p -> do                 -- '.' alpha ...
        next (C.letpath v)
          <|> return (C.decl p)
          
      Priv _ -> next (C.letpath v)  -- alpha ...
  where
    next x = liftA2 C.letrec (destructure1 x) (eqsep >> reads)

        

-- | Parse a destructuring statement
destructurestmt :: Rec g a => Parser a -> Parser g
destructurestmt reads =
  do
    l <- destructure
    C.letrec l <$> (eqsep >> reads)
    
                    
                    
-- | Parse a valid lhs pattern for an assignment
patt :: Patt p => Parser p
patt = 
  ((C.letpath <$> readsMy) >>= destructure1)
    <|> destructure
    <?> "set expression"
        

-- | Parse a destructure expression      
destructure :: Patt p => Parser p
destructure = C.ungroup <$> tuple patt >>= destructure1
    
    
-- | Parse remaining chain of patterns
destructure1 :: Patt p => p -> Parser p
destructure1 x =
  (tuple patt >>= destructure1 . C.letungroup x)
    <|> return x
    
    
-- | Parse a top-level sequence of statements
header :: Parser Import
header = readsMy <* ellipsissep


program :: C.Program r Import => Parser r
program = do
    m <- P.optionMaybe header
    x <- recstmt syntax
    (do
      semicolonsep
      xs <- msepEndBy (pure <$> recstmt syntax) semicolonsep
      (return . C.program m) (option x (x<>) xs))
      <|> return (C.program m x)
    <* P.eof

