{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts, RankNTypes, UndecidableInstances #-}

-- | Parsers for my syntax types

module My.Parser
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
  
  -- util parsers
  , ident, integer
  , spaces, comment, point, stringfragment, escapedchars, identpath
  , commasep, ellipsissep, semicolonsep, eqsep
  , parens, braces, staples
  , readAnd, readOr
  , readEq, readNe,  readLt, readGt, readLe, readGe
  , readAdd, readSub, readProd, readDiv, readPow
  , readNot, readNeg
  
  -- util show
  , showLitString, showLitText, showText, showIdent, showKey, showImport
  , showBinop, showUnop
  )
  where
  
import My.Types.Parser
import qualified Data.Text as T
import qualified Text.Parsec as P
import Text.Parsec ((<|>), (<?>), try, parse)
import Text.Parsec.Text  (Parser)
import Numeric (readHex, readOct)
import Control.Applicative (liftA2)
import Data.Char (showLitChar)
import Data.Foldable (foldl', concat, toList)
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import Data.Semigroup ((<>))
import Data.Function ((&))
import Data.Bifunctor (bimap)
import Control.Monad.State


-- | Extract a valid my-language source text representation from a
--   Haskell data type representation
class ShowMy a where
  showMy :: a -> String
  showMy x = showsMy x ""
  
  showsMy :: a -> String -> String
  showsMy x s = showMy x ++ s
  

showSep :: ShowMy a => String -> a -> ShowS
showSep sep a = showString sep . showsMy a


showLitString :: String -> ShowS
showLitString []          s = s
showLitString ('"' : cs)  s =  "\\\"" ++ (showLitString cs s)
showLitString (c   : cs)  s = showLitChar c (showLitString cs s)


showLitText :: T.Text -> ShowS
showLitText = showLitString . T.unpack


showText :: T.Text -> ShowS
showText = (++) . T.unpack

   
-- | Parse source text into a Haskell data type representing my language
class ReadMy a where readsMy :: Parser a

  
readMy :: ReadMy a => String -> a
readMy = either (errorWithoutStackTrace "readMy") id . parse (readsMy <* P.eof) "readMy" . T.pack


readIOMy :: ReadMy a => String -> IO a
readIOMy = either (ioError . userError . show) return
  . parse (readsMy <* P.eof) "readMy" . T.pack

     
      
-- | Parse a comment
comment :: Parser T.Text
comment = (do
  try (P.string "//")
  s <- P.manyTill P.anyChar (try ((P.endOfLine >> return ()) <|> P.eof))
  return (T.pack s))
    <?> "comment"
    
    
-- | Parse whitespace and comments
spaces :: Parser ()
spaces = P.spaces >> P.optional (comment >> spaces) 

    
-- | Parse any valid numeric literal
number :: Parser (Expr a)
number =
  (binary
    <|> octal
    <|> hexidecimal
    <|> decfloat
    <?> "number literal")
    <* spaces
    
    
-- | Parse a valid binary number
binary :: Parser (Expr a)
binary =
  do
    try (P.string "0b")
    IntegerLit . bin2dig <$> integer (P.oneOf "01")
    where
      bin2dig =
        foldl' (\digint x -> 2 * digint + (if x=='0' then 0 else 1)) 0

        
-- | Parse a valid octal number
octal :: Parser (Expr a)
octal =
  try (P.string "0o") >> integer P.octDigit >>= return . IntegerLit . oct2dig
    where
      oct2dig x =
        fst (readOct x !! 0)

        
-- | Parse a valid hexidecimal number
hexidecimal :: Parser (Expr a)
hexidecimal =
  try (P.string "0x") >> integer P.hexDigit >>= return . IntegerLit . hex2dig
  where 
    hex2dig x =
      fst (readHex x !! 0)
  
  
  
-- | Parse a sequence of underscore spaced digits
integer :: Parser a -> Parser [a]
integer d =
  (P.sepBy1 d . P.optional) (P.char '_')
  
  
-- | Parse a single decimal point / field accessor
--   (requires disambiguation from extension dots)
point :: Parser Char
point = try (P.char '.' <* P.notFollowedBy (P.char '.')) <* spaces
    
    
-- | Parser for valid decimal or floating point number
decfloat :: Parser (Expr a)
decfloat =
  prefixed
    <|> unprefixed
  where
    prefixed =
      do
        try (P.string "0d")
        IntegerLit . read <$> integer P.digit
        
    unprefixed =
      do
        xs <- integer P.digit
        fracnext xs                             -- int frac
                                                -- int frac exp
          <|> expnext xs                        -- int exp
          <|> (return . IntegerLit) (read xs)   -- int
          
    fracnext xs =
      do 
        y <- point
        m <- P.optionMaybe (integer P.digit)
        case m of
          Nothing ->
            -- frac
            (return . NumberLit . read) (xs ++ [y, '0'])
            
          Just ys ->
            expnext (xs ++ [y] ++ ys)   -- frac exp
              <|>
                (return . NumberLit . read) (xs ++ [y] ++ ys)
                                      -- frac
          
    expnext xs =
      do 
        e <- P.oneOf "eE"
        sgn <- P.option [] (P.oneOf "+-" >>= return . pure)
        ys <- integer P.digit
        (return . NumberLit . read) (xs ++ e:sgn ++ ys)


-- | Parse a double-quote wrapped string literal
string :: Parser (Expr a)
string =
  TextLit . T.pack <$> stringfragment <?> "string literal"

  
stringfragment :: Parser String
stringfragment =
  P.between
    (P.char '"')
    (P.char '"' >> spaces)
    (P.many (P.noneOf "\"\\" <|> escapedchars))

    
-- | Parse an escaped character
escapedchars :: Parser Char
escapedchars =
  do
    P.char '\\'
    x <- P.oneOf "\\\"nrt"
    return
      (case x of
        '\\' ->
          x
          
        '"'  ->
          x
          
        'n'  ->
          '\n'
      
        'r'  ->
          '\r'
        
        't'  ->
          '\t')

          
          
instance ReadMy Ident where
  readsMy = ident
  
ident :: Parser Ident
ident = 
  (do
    x <- P.letter
    xs <- P.many P.alphaNum
    spaces
    (return . I_ . T.pack) (x:xs))
      <?> "identifier"

  
instance ShowMy Ident where
  showsMy = showIdent

showIdent :: Ident -> ShowS
showIdent (I_ s) = showText s
    

-- | Alternative filepath style of ident with slashs to represent import paths
--   (not used)
identpath :: Parser Ident
identpath = (do
    x <- P.letter
    xs <- rest
    spaces
    (return . I_ . T.pack) (x:xs))
    <?> "identifier"
  where
    rest = 
      alphanumnext <|> slashnext <|> return []
        
    alphanumnext = do
      x <- P.alphaNum
      xs <- rest
      return (x:xs)
      
    slashnext = do
      (c,x) <- try ((,) <$> P.char '/' <*> P.letter)
      xs <- rest
      return (c:x:xs)
      
      
instance ReadMy Key where
  readsMy = readKey
  
readKey :: Parser Key
readKey = point >> K_ <$> ident <?> "field name"

  
instance ShowMy Key where
  showsMy = showKey
  
showKey :: Key -> ShowS
showKey (K_ s) = showChar '.' . showIdent s
  
  
instance ReadMy Import where
  readsMy = readImport
  
readImport :: Parser Import
readImport = P.string "@use" >> spaces >> Use <$> readsMy
  
  
instance ShowMy Import where
  showsMy = showImport
  
showImport :: Import -> ShowS
showImport (Use s) = showString "@use " . showsMy s

    
instance (ReadMy b) => ReadMy (Field b) where
  readsMy = liftA2 At readsMy readsMy

  
instance (ShowMy b) => ShowMy (Field b) where
  showsMy (a `At` t) = showsMy a . showsMy t
        
        
instance (ReadMy b) => ReadMy (Path b) where
  readsMy = readsMy >>= path


instance (ShowMy b, ShowMy (Field (Path b))) => ShowMy (Path b) where
  showsMy (Pure a) = showsMy a
  showsMy (Free f) = showsMy f
  

-- | Parse a relative path
path :: b -> Parser (Path b)
path = rest . Pure
  where
    rest x =
      (readsMy >>= rest . Free . At x)
        <|> return x
        
       
instance (ReadMy a, ReadMy b) => ReadMy (Vis a b) where
  readsMy =
    (Pub <$> readsMy)
      <|> (Priv <$> readsMy)

      
instance (ShowMy a, ShowMy b) => ShowMy (Vis a b) where
  showsMy (Priv l) = showsMy l
  showsMy (Pub t) = showsMy t
  
  
instance (ReadMy a, ReadMy b) => ReadMy (Res a b) where
  readsMy =
    (Ex <$> readsMy)
      <|> (In <$> readsMy)
      
      
instance (ShowMy a, ShowMy b) => ShowMy (Res a b) where
  showsMy (Ex a) = showsMy a
  showsMy (In b) = showsMy b


instance ReadMy (Expr (Name Ident Key Import)) where
  readsMy =
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
              
              
instance (ShowMy a) => ShowMy (Expr a) where
  showsMy e = case e of
    IntegerLit n  -> shows n
    NumberLit n   -> shows n
    TextLit x   -> showChar '"' . showLitText x . showChar '"'
    Var x         -> showsMy x
    Get p         -> showsMy p
    Group b       -> showsMy b
    Extend e b    -> showParen t (showsMy e) . showChar ' ' . showsMy b where
      t = case e of Unop{} -> True; Binop{} -> True; _ -> False
    Unop o a      -> showUnop o . showParen t (showsMy a)  where 
      t = case a of Binop{} -> True; _ -> False
    Binop o a b   -> showArg a . showChar ' ' . showBinop o
      . showChar ' ' . showArg b where
        showArg a = showParen t (showsMy a) where 
          t = case a of Binop p _ _ -> prec p o; _ -> False
          
          
-- | Parse an expression observing operator precedence
orexpr :: Parser (Expr (Name Ident Key Import))
orexpr =
  P.chainl1 andexpr (Binop <$> readOr)

      
andexpr :: Parser (Expr (Name Ident Key Import))
andexpr =
  P.chainl1 cmpexpr (Binop <$> readAnd)

        
cmpexpr :: Parser (Expr (Name Ident Key Import))
cmpexpr =
  do
    a <- addexpr
    (do
       s <- op
       b <- addexpr
       return (s a b))
      <|> return a
  where
    op = Binop <$> (readGt <|> readLt <|> readEq <|> readNe <|> readGe <|> readLe)
   
   
addexpr :: Parser (Expr (Name Ident Key Import))
addexpr =
  P.chainl1 mulexpr (Binop <$> (readAdd <|> readSub))


mulexpr :: Parser (Expr (Name Ident Key Import))
mulexpr =
  P.chainl1 powexpr (Binop <$> (readProd <|> readDiv))


powexpr :: Parser (Expr (Name Ident Key Import))
powexpr =
  P.chainl1 term (Binop <$> readPow)
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
unop :: Parser (Expr (Name Ident Key Import))
unop = Unop <$> readsMy <*> pathexpr
        
        
-- | Parse a chain of field accesses and extensions
pathexpr :: Parser (Expr (Name Ident Key Import))
pathexpr =
  first >>= rest
  where
    next x =
      (Extend x <$> readsMy)
        <|> (Get . At x <$> readsMy)
    
    
    rest x =
      (next x >>= rest)
        <|> return x
    
    
    first =
      string                      -- '"' ...
        <|> parens disambigTuple  -- '(' ...
        <|> (Group <$> block)     -- '{' ...
        <|> number                -- digit ...
        <|> (Var <$> readsMy)     -- '.' alpha ...
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
    disambigTuple :: Parser (Expr (Name Ident Key Import))
    disambigTuple = (readsMy >>= \ e -> case tryStmt e of 
      Nothing -> return e
      Just (Pub p) ->
        eqNext p                -- '=' ...
          <|> sepNext (Pub p)   -- ',' ...
          <|> return e          -- ')' ...
      Just (Priv p) ->
        sepNext (Priv p)        -- ',' ...
          <|> return e)         -- ')' ...
        <|> (return . Group) (Tup [])
      where
        -- | Try to interpret an expression as the start of a tuple
        --   statement
        tryStmt
          :: Expr (Name Ident Key Import)
          -> Maybe (Vis (Path Ident) (Path Key))
        tryStmt (Var x) = case x of
          Ex _ -> Nothing
          In v -> Just (bimap Pure Pure v)
        tryStmt (Get (e `At` x)) = (bimap wrap wrap) <$> tryStmt e where
          wrap :: Path a -> Path a
          wrap p = Free (p `At` x)
        tryStmt _ = Nothing
        
        eqNext
          :: Path Key
          -> Parser (Expr (Name Ident Key Import))
        eqNext p = liftA2 go (eqsep >> readsMy) tuple1 where
          go x xs = (Group . Tup) (Let p x:xs)
          
        sepNext
          :: Vis (Path Ident) (Path Key)
          -> Parser (Expr (Name Ident Key Import))
        sepNext p = Group . Tup . (Pun p:) <$> tuple1

        
-- | Parse a block expression
instance (ReadMy a) => ReadMy (Group a) where
  readsMy = block <|> (Tup <$> tuple)
  
  
instance (ShowMy a) => ShowMy (Group a) where
  showsMy b = case b of
    Tup []    -> showString "()"
    Tup [x]     -> showString "( " . showsMy x . showString ",)"
    Tup (x:xs)  -> showString "( " . showsMy x . flip (foldr (showSep ", ")) xs
      . showString " )"
    Block []      -> showString "{}"
    Block (y:ys)  -> showString "{ " . showsMy y
      . flip (foldr (showSep "; ")) ys . showString " }"
      
        
-- | Parse statement equals definition
eqsep :: Parser ()
eqsep = P.char '=' >> spaces
            
    
-- | Parse statement separators
semicolonsep :: Parser ()
semicolonsep =
  P.char ';' >> spaces
  
  
commasep :: Parser ()
commasep =
  P.char ',' >> spaces
  
  
ellipsissep :: Parser ()
ellipsissep =
  try (P.string "..." <* P.notFollowedBy (P.char '.')) >> spaces

  
-- | Parse different bracket types
braces :: Parser a -> Parser a
braces =
  P.between
    (P.char '{' >> spaces)
    (P.char '}' >> spaces)

    
parens :: Parser a -> Parser a
parens =
  P.between
    (P.char '(' >> spaces)
    (P.char ')' >> spaces)
    

staples :: Parser a -> Parser a
staples =
  P.between
    (P.char '[' >> spaces)
    (P.char ']' >> spaces)
    
        
-- | Parse either an expression wrapped in parens or a tuple form block
tuple :: ReadMy a => Parser [a]
tuple = parens (some <|> return []) <?> "tuple"
  where
    some = liftA2 (:) readsMy tuple1
    
    
tuple1 :: ReadMy a => Parser [a]
tuple1 = commasep >> P.sepEndBy readsMy commasep

        
block :: ReadMy a => Parser (Group a)
block = Block <$> braces (P.sepEndBy readsMy semicolonsep) <?> "block"
          
          
-- | Parse binary operators
readOr, readAnd, readEq, readNe, readLt, readGt, readLe, readGe, readAdd,
  readSub, readProd, readDiv, readPow  :: Parser Binop
readOr = P.char '|' >> spaces >> return Or
readAnd = P.char '&' >> spaces >> return And
readEq = try (P.string "==") >> spaces >> return Eq
readNe = try (P.string "!=") >> spaces >> return Ne
readLt = try (P.char '<' >> P.notFollowedBy (P.char '=')) >> spaces >> return Lt
readGt = try (P.char '>' >> P.notFollowedBy (P.char '=')) >> spaces >> return Gt
readLe = try (P.string "<=") >> spaces >> return Le
readGe = try (P.string ">=") >> spaces >> return Ge
readAdd = P.char '+' >> spaces >> return Add
readSub = P.char '-' >> spaces >> return Sub
readProd = P.char '*' >> spaces >> return Prod
readDiv = P.char '/' >> spaces >> return Div
readPow = P.char '^' >> spaces >> return Pow


instance ReadMy Binop where
  readsMy = P.choice   
    [ readOr
    , readAnd
    , readLt <|> readGt <|> readEq <|> readNe <|> readLe <|> readGe
    , readSub <|> readAdd
    , readDiv <|> readProd
    , readPow
    ] <?> "binary operator"
  
showBinop :: Binop -> ShowS
showBinop Add   = showChar '+'
showBinop Sub   = showChar '-'
showBinop Prod  = showChar '*'
showBinop Div   = showChar '/'
showBinop Pow   = showChar '^'
showBinop And   = showChar '&'
showBinop Or    = showChar '|'
showBinop Lt    = showChar '<'
showBinop Gt    = showChar '>'
showBinop Eq    = showString "=="
showBinop Ne    = showString "!="  
showBinop Le    = showString "<="
showBinop Ge    = showString ">="
          

instance ShowMy Binop where
  showsMy = showBinop
  
  
-- | Parse unary operators
readNeg, readNot :: Parser Unop
readNeg = P.char '-' >> spaces >> return Neg
readNot = P.char '!' >> spaces >> return Not


instance ReadMy Unop where
  readsMy = readNeg <|> readNot <?> "unary operator"


showUnop :: Unop -> ShowS
showUnop Neg = showChar '-'
showUnop Not = showChar '!'


instance ShowMy Unop where
  showsMy = showUnop


-- | Parse a statement of a block expression
instance (ReadMy a) => ReadMy (RecStmt a) where
  readsMy = 
    letrecstmt        -- '.' alpha ...
                            -- alpha ...
      <|> destructurestmt   -- '(' ...
      <?> "statement"
    
  
instance (ShowMy a) => ShowMy (RecStmt a) where
  showsMy (Decl l) = showsMy l
  showsMy (l `LetRec` r) = showsMy l . showString " = " . showsMy r
    
    
instance (ReadMy a) => ReadMy (Stmt a) where
  readsMy = do
    v <- readsMy
    case v of
      Priv _ -> return (Pun v)          -- alpha ...
      Pub p ->                          -- '.' alpha ...
        (Let p <$> (eqsep >> readsMy))
          <|> return (Pun v)
      
  
instance (ShowMy a) => ShowMy (Stmt a) where 
  showsMy (Pun l) = showsMy l
  showsMy (l `Let` a) = showsMy l . showString " = " . showsMy a


-- | Parse a recursive let statement
letrecstmt :: ReadMy a => Parser (RecStmt a)
letrecstmt =
  do
    v <- readsMy
    case v of
      Pub p -> do                 -- '.' alpha ...
        next (LetPath v)
          <|> return (Decl p)
          
      Priv _ -> next (LetPath v)  -- alpha ...
  where
    next x = liftA2 LetRec (ungroup1 x) (eqsep >> readsMy)

        

-- | Parse a destructuring statement
destructurestmt :: (ReadMy a) => Parser (RecStmt a)
destructurestmt =
  do
    l <- ungroup
    LetRec l <$> (eqsep >> readsMy)
    
                    
                    
-- | Parse a valid lhs pattern for an assignment
instance ReadMy Patt where
  readsMy = 
    ((LetPath <$> readsMy) >>= ungroup1)
      <|> ungroup
      <?> "set expression"
    
    
instance ShowMy Patt where
  showsMy e = case e of
    LetPath x       -> showsMy x
    Ungroup xs       -> showDes xs
    LetUngroup l xs  -> showsMy l . showChar ' ' . showDes xs
    where
      showDes [] = showString "()"
      showDes [x] = showString "( " . showsMy x . showString ",)"
      showDes (x:xs) = showString "( " . showsMy x . flip (foldr (showSep ", ")) xs
        . showString " )"
        

-- | Parse a ungroup expression      
ungroup :: Parser Patt
ungroup = Ungroup <$> tuple >>= ungroup1
    
    
-- | Parse remaining chain of patterns
ungroup1 :: Patt -> Parser Patt
ungroup1 x =
  (tuple >>= ungroup1 . LetUngroup x)
    <|> return x
    
    
-- | Parse a top-level sequence of statements
header :: Parser Import
header = readsMy <* ellipsissep


instance ReadMy (Program Import) where
  readsMy = (do
    m <- P.optionMaybe header
    x <- readsMy
    (do
      semicolonsep
      xs <- P.sepEndBy readsMy semicolonsep
      (return . Program m) (x:|xs))
      <|> (return . Program m) (pure x))
    <* P.eof
    

instance ShowMy a => ShowMy (Program a) where
  showsMy (Program m (x:|xs)) =
    maybe id showHeader m . showsMy x  . flip (foldr (showSep ";\n\n")) xs
    where
      showHeader m = showsMy m . showString "...\n\n"

