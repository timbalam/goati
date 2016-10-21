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
  , lhs
  , lroute
  , lnode
  , rhs
  , unop
  , and_expr
  , rroute
  , rnode
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
string = P.sepBy1 string_fragment spaces >>= return . T.String . concat
  where
    string_fragment = P.between (P.char '"') (P.char '"') (P.many $ P.noneOf "\"\\" <|> escapedChars)

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

-- | Parse a local route
relative_route :: Parser T.RelativeRoute
relative_route =
  do{ P.char '.'
    ; spaces
    ; x <- name
    ; do{ ys <- relative_route
        ; return (T.RelativeRoute x ys)
        }
      <|> return (T.Name x)
    }
    
lhs :: Parser T.Lval
lhs = lroute <|> lnode

-- | Parse a route
lroute :: Parser T.Lval
lroute =
  (relative_route >>= return . T.LlocalRoute)
  <|> absolute_route
  <?> "route"
  where
    absolute_route =
      do{ x <- ident
        ; do{ y <- relative_route
            ; return $ T.LabsoluteRoute x y
          }
          <|> (return $ T.Lident x)
        }

-- | Parse an statement break
stmt_break = try $ P.between spaces spaces (P.char ';')

reversible_assign_stmt :: Parser T.ReversibleStmt
reversible_assign_stmt = 
  do{ x <- relative_route
    ; spaces
    ; P.char '='
    ; spaces
    ; y <- lhs
    ; return $ T.ReversibleAssign x y
    }

reversible_unpack_stmt :: Parser T.ReversibleStmt
reversible_unpack_stmt =
  do{ P.char '*'
    ; x <- lroute
    ; return $ T.ReversibleUnpack x
    }

-- | Parse a destructuring statement
lnode :: Parser T.Lval
lnode =
  P.between (P.char '{' >> spaces) (spaces >> P.char '}') lnode_body
    >>= return . T.Lnode
  where
    lnode_body = unpack_first_body <|> assign_first_body
    unpack_first_body =
      do{ x <- reversible_unpack_stmt
        ; xs <- P.many1 (stmt_break >> reversible_assign_stmt)
        ; return (x:xs)
        }
    assign_first_body =
      do{ x <- reversible_assign_stmt
        ; do{ stmt_break
            ; xs <- unpack_rest_body <|> assign_first_body
            ; return (x:xs)
            }
          <|> return [x]
        }
    unpack_rest_body =
      do{ x <- reversible_unpack_stmt
        ; xs <- P.many (stmt_break >> reversible_assign_stmt)
        ; return (x:xs)
        }
  
-- | Parse an expression with binary operations
rhs :: Parser T.Rval
rhs = or_expr
      
bracket :: Parser T.Rval
bracket = P.between (P.char '(' >> spaces) (spaces >> P.char ')') rhs

rroute :: Parser T.Rval
rroute = local_route <|> absolute_route
  where
    local_route =
      do{ y <- relative_route
        ; let x = T.RlocalRoute y
        ; do{ s <- bracket
            ; rest (x `T.App` s)
            }
          <|> return x
        }
    absolute_route =
      do{ x <- routable
        ; rest x
        }
    rest x =
      do{ y <- relative_route
        ; let x' = T.RabsoluteRoute x y
        ; do{ s <- bracket
            ; rest (x' `T.App` s)
            }
          <|> return x'     
        }
      <|> return x
    routable =
      string
      <|> bracket
      <|> number
      <|> rnode
      <|> (ident >>= return . T.Rident)
      
      
-- | Parse an unpack statement
unpack_stmt :: Parser T.Stmt
unpack_stmt = 
  do{ P.char '*'
    ; x <- rroute 
    ; return $ T.Unpack x
    }

-- | Parse an assign statement
assign_stmt :: Parser T.Stmt
assign_stmt =
  do{ x <- lhs
    ; spaces
    ; P.char '='
    ; spaces
    ; y <- rhs
    ; return $ T.Assign x y
    }

-- | Parse an eval statement
eval_stmt :: Parser T.Stmt
eval_stmt = 
  do{ x <- rhs
    ; return $ T.Eval x
    }
    
-- | Parse any statement
stmt :: Parser T.Stmt
stmt = unpack_stmt
  <|> try assign_stmt
  <|> eval_stmt
  <?> "statement"
      

-- | Parse a curly-brace wrapped sequence of statements
rnode :: Parser T.Rval
rnode =
  P.between
    (P.char '{' >> spaces)
    (spaces >> P.char '}')
    (P.sepBy1 stmt stmt_break)
  >>= return . T.Rnode
    
-- | Parse an unary operator
unop :: Parser T.Rval
unop =
  do{ s <- unop_symbol
    ; spaces
    ; x <- rroute
    ; return $ T.Unop s x
    }
  where
    unop_symbol =
      (P.char '-' >> return T.Neg)
      <|> (P.char '!' >> return T.Not)

binop_chain_expr :: Parser T.Rval -> Parser (T.Rval -> T.Rval -> T.Rval) -> Parser T.Rval
binop_chain_expr p b = try chain <|> p
  where
    chain = P.chainl1 p (P.between spaces spaces b)
      
or_expr :: Parser T.Rval
or_expr = binop_chain_expr and_expr or_ops
  where
    or_ops = P.char '|' >> return (T.Binop T.Or)

and_expr :: Parser T.Rval
and_expr = binop_chain_expr cmp_expr and_ops
  where
    and_ops = P.char '&' >> return (T.Binop T.And)

cmp_expr :: Parser T.Rval
cmp_expr = try cmp_pair <|> add_expr
  where
    cmp_pair = 
      do{ a <- add_expr
        ; s <- P.between spaces spaces cmp_ops
        ; b <- add_expr
        ; return (s a b)
        }
    cmp_ops =
      (P.char '>' >> return (T.Binop T.Gt))
      <|> (P.char '<' >> return (T.Binop T.Lt))
      <|> try (P.string "==" >> return (T.Binop T.Eq))
      <|> try (P.string ">=" >> return (T.Binop T.Ge))
      <|> try (P.string "<=" >> return (T.Binop T.Le))
   
add_expr = binop_chain_expr mul_expr add_ops
  where
    add_ops =
      (P.char '+' >> return (T.Binop T.Add))
      <|> (P.char '-' >> return (T.Binop T.Sub))

mul_expr = binop_chain_expr pow_expr mul_ops
  where
    mul_ops =
      (P.char '*' >> return (T.Binop T.Prod))
      <|> (P.char '/' >> return (T.Binop T.Div))

pow_expr = binop_chain_expr term pow_ops
  where
    pow_ops = P.char '^' >> return (T.Binop T.Pow)
    term = unop <|> rroute
    
-- | Parse a top-level sequence of statements
program :: Parser [T.Stmt]
program = P.between spaces spaces (P.sepBy1 stmt stmt_break)


