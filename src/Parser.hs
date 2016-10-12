module Parser
  ( float
  , decimal
  , binary
  , octal
  , hexidecimal
  , number
  , string
  , ident
  , name
  , relative_route
  , route
  , lhs
  , rhs
  , stmt
  , node
  , application
  , program
  ) where
import qualified Text.Parsec as P hiding
  ( try )
import Text.Parsec
  ( (<|>)
  , (<?>)
  , try
  )
import Text.Parsec.String
  ( Parser
  )
import Numeric
  ( readHex
  , readOct
  )
import qualified Types as T
  
-- | Parser that succeeds when consuming a sequence of underscore spaced digits
integer :: Parser Char -> Parser String
integer d = P.sepBy1 d (P.optional $ P.char '_')
    
-- | Parser for valid floating point number
float :: Parser T.Rval
float =
  do{ xs <- integer P.digit
    ; y <- P.char '.'
    ; ys <- P.option "0" (integer P.digit)
    ; return $ T.Number $ read $ (xs ++ [y] ++ ys)
    }

-- | Parser for valid decimal number
decimal :: Parser T.Rval
decimal = P.optional (P.string "0d") >> integer P.digit >>= return . T.Number . read

-- | Parser for valid binary number
binary :: Parser T.Rval
binary = (try $ P.string "0b") >> integer (P.oneOf "01") >>= return . T.Number . bin2dig
  where bin2dig = foldr (\x digint -> 2 * digint + (if x=='0' then 0 else 1)) 0

-- | Parser for valid octal number
octal :: Parser T.Rval
octal = (try $ P.string "0o") >> integer P.octDigit >>= return . T.Number . oct2dig
  where oct2dig x = fst $ readOct x !! 0

-- | Parser for valid hexidecimal number
hexidecimal :: Parser T.Rval
hexidecimal = (try $ P.string "0x") >> integer P.hexDigit >>= return . T.Number . hex2dig
  where hex2dig x = fst $ readHex x !! 0
                 
-- | Parser for valid numeric value
number :: Parser T.Rval
number = binary <|> octal <|> hexidecimal <|> try float <|> decimal <?> "number"

-- | Parser that succeeds when consuming an escaped character.
escapedChars =
  do{ P.char '\\'
    ; x <- P.oneOf "\\\"nrt"
    ; return $
      case
        x
      of
      { '\\' -> x
      ; '"'  -> x
      ; 'n'  -> '\n'
      ; 'r'  -> '\r'
      ; 't'  -> '\t'
      }
    }

-- | Parser that succeeds when consuming a double-quote wrapped string.
string :: Parser T.Rval
string = (P.between (P.char '"') (P.char '"') (P.many $ P.noneOf "\"\\" <|> escapedChars) >>= return . T.String) <?> "string"

-- | Parser that succeeds when consuming a valid identifier string.
ident :: Parser T.Ident
ident =
  do{ x <- P.letter
    ; xs <- P.many P.alphaNum
    ; return $ T.Ident (x:xs)
    }
    
-- | Parser that parses whitespace
spaces = P.spaces

-- | Parse a valid node name
name :: Parser T.Name
name =  (ident >>= return . T.Ref)
    <|> (P.between (P.char '(' >> spaces) (spaces >> P.char ')') rhs >>= return . T.Key)

-- | Parse an statement break
--stmt_break = try $ P.between spaces spaces (P.char ';' >> return ())

-- | Parse a local route
relative_route :: Parser T.RelativeRoute
relative_route =
  P.many1 (P.char '.' >> spaces >> name)
    >>= return . T.RelativeRoute

-- | Parse a route
route :: Parser T.Lval
route =
  (relative_route >>= return . T.LocalRoute)
  <|> absolute_route
  <?> "route"
  where
    absolute_route =
      do{ x <- ident
        ; y <- P.option (T.RelativeRoute []) relative_route
        ; return $ T.AbsoluteRoute x y
        }

lhs :: Parser T.Lval
lhs = route <|> reversible_node

stmt_break = try $ P.between spaces spaces (P.char ';')

assign_reversible_stmt :: Parser T.ReversibleStmt
assign_reversible_stmt = 
  do{ x <- relative_route
    ; spaces
    ; P.char '='
    ; spaces
    ; y <- lhs
    ; return $ T.ReversibleAssign x y
    }

unpack_reversible_stmt :: Parser T.ReversibleStmt
unpack_reversible_stmt =
  do{ P.char '*'
    ; x <- route
    ; return $ T.ReversibleUnpack x
    }

-- | Parse a destructuring statement
reversible_node :: Parser T.Lval
reversible_node =
  P.between (P.char '{' >> spaces) (spaces >> P.char '}') reversible_node_body
    >>= return . T.ReversibleNode
  where
    reversible_node_body =  unpack_first_body
                        <|> assign_first_body
    unpack_first_body =
      do{ x <- unpack_reversible_stmt
        ; xs <- P.many1 (stmt_break >> assign_reversible_stmt)
        ; return (x:xs)
        }
    assign_first_body =
      do{ xs <- P.sepBy1 assign_reversible_stmt stmt_break
        ; ys <- P.option [] (stmt_break >> unpack_rest_body)
        ; return (xs++ys)
        }
    unpack_rest_body =
      do{ x <- unpack_reversible_stmt
        ; xs <- P.many (stmt_break >> assign_reversible_stmt)
        ; return (x:xs)
        }

-- | Parse an rvalue
rhs :: Parser T.Rval
rhs = binop oplist <|> expr

expr :: Parser T.Rval
expr =
  unop
  <|> string
  <|> P.between (P.char '(' >> spaces) (spaces >> P.char ')') rhs
  <|> number
  <|> node
      
-- | Parse an unpack statement
unpack_stmt :: Parser T.Stmt
unpack_stmt = 
  do{ P.char '*'
    ; x <- node
    ; return $ T.Unpack x
    }

-- | Parse an eval statement
eval_stmt :: Parser T.Stmt
eval_stmt = 
  do{ x <- rhs
    ; return $ T.Eval x
    }
    
-- | Parse any statement
stmt = unpack_stmt
  <|> try assign_stmt
  <|> eval_stmt
  <?> "statement"
      

-- | Parse a curly-brace wrapped sequence of statements
node :: Parser T.Rval
node =
  P.between
    (P.char '{' >> spaces)
    (spaces >> P.char '}')
    P.sepBy1 stmt stmt_break
  >>= return . T.Node

-- | Parse an application
application :: Parser T.Rval
application =
  do{ x <- rhs
    ; y <- P.between (P.char '(' >> spaces) (spaces >> P.char ')') rhs
    ; return $ T.App x y
    }
    
-- | Parse an unary operator
unop :: Parser T.Rval
unop =
  do{ s <- unop_symbol
    ; spaces
    ; x <- rhs
    ; return $ T.Unop s x
    }
  where
    unop_symbol =
      (P.char '-' >> return T.Neg)
      <|> (P.char '!' >> return T.Not)

binop :: [Chainable] -> Parser T.Rval
binop [] = expr
binop ((Chainable o):os) = P.chainl1 (binop os) (P.between spaces spaces o >>= return . T.Binop)
binop ((Unchainable o):os) =
  do{ x <- binop os
    ; do{ s <- P.between spaces spaces o
        ; y <- binop os
        ; return $ T.Binop s x y
        }
      <|> return x
    }

data Chainable = Chainable (Parser T.Binop) | Unchainable (Parser T.Binop)

oplist :: [Chainable]
oplist =
  [ Chainable $ P.char '|' >> return T.Or
  , Chainable $ P.char '&' >> return T.And
  , Unchainable cmp_ops
  , Chainable add_ops
  , Chainable mul_ops
  , Chainable $ P.char '^' >> return T.Pow
  ]
  where
    cmp_ops =
      (P.char '>' >> return T.Gt)
      <|> (P.char '<' >> return T.Lt)
      <|> (try P.string "==" >> return T.Eq)
      <|> (try P.string ">=" >> return T.Ge)
      <|> (try P.string "<=" >> return T.Le)
    add_ops =
      (P.char '+' >> return T.Add)
      <|> (P.char '-' >> return T.Sub)
    mul_ops =
      (P.char '*' >> return T.Prod)
      <|> (P.char '/' >> return T.Div)
    
-- | Parse a top-level sequence of statements
program :: Parser [T.Stmt]
program = P.between spaces spaces (P.sepBy1 stmt stmt_break)


