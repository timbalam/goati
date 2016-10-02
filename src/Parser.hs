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
  , expr
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

-- | Parse an expression break
expr_break = try $ P.between spaces spaces (P.char ';') >> return ()

-- | Parse a local route
relative_route :: Parser T.RelativeRoute
relative_route =
  P.many1 (P.char '.' >> spaces >> name)
    >>= return . T.RelativeRoute

-- | Parse a route
route :: Parser T.Lval
route =  (relative_route >>= return . T.LocalRoute)
     <|> absolute_route
     <?> "route"
  where
    absolute_route =
      do{ x <- ident
        ; y <- P.option (T.RelativeRoute []) relative_route
        ; return $ T.AbsoluteRoute x y
        }

lhs :: Parser T.Lval
lhs =  route
   <|> reversible_node

assign_reversible_expr :: Parser T.ReversibleExpr
assign_reversible_expr = 
  do{ x <- relative_route
    ; spaces
    ; P.char '='
    ; spaces
    ; y <- lhs
    ; return $ T.ReversibleAssign x y
    }

unpack_reversible_expr :: Parser T.ReversibleExpr
unpack_reversible_expr = try (P.string "...") >> route >>= return . T.ReversibleUnpack

-- | Parse a destructuring expression
reversible_node :: Parser T.Lval
reversible_node =
  P.between (P.char '{' >> spaces) (spaces >> P.char '}') reversible_node_body
    >>= return . T.ReversibleNode
  where
    reversible_node_body =  unpack_first
                        <|> assign_next
    unpack_first =
      do{ x <- unpack_reversible_expr
        ; xs <- P.many1 (expr_break >> assign_reversible_expr)
        ; return (x:xs)
        }
    assign_or_unpack_rest =  unpack_next
                         <|> assign_next
    unpack_next =
      do{ x <- unpack_reversible_expr
        ; xs <- P.many (expr_break >> assign_reversible_expr)
        ; return (x:xs)
        }
    assign_next =
      do{ x <- assign_reversible_expr
        ; xs <- P.option [] (expr_break >> assign_or_unpack_rest)
        ; return (x:xs)
        }
            
-- | Parse an rvalue
rhs :: Parser T.Rval
rhs =  string
   <|> number
   <|> (route >>= return . T.Lval)
   <|> node

-- | Parse an unpack expression
unpack_expr :: Parser T.Expr
unpack_expr =
  try (P.string "...")
    >> ( node <|> (route >>= return . T.Lval) )
    >>= return . T.Unpack

-- | Parse an eval expression
eval_expr :: Parser T.Expr
eval_expr = rhs >>= return . T.Eval
    
-- | Parse any expression
expr =  unpack_expr
    <|> lval_first
    <|> eval_expr
    <?> "expression"
    where
      lval_first =
        do{ x <- lhs
          ; assign_lval x <|> eval_lval x
          }
      assign_lval x =
        try (spaces >> P.char '=' >> spaces)
              >> rhs
              >>= return . T.Assign x
      eval_lval = return . T.Eval . T.Lval
      

-- | Parse a curly-brace wrapped sequence of expressions
node_body :: Parser [T.Expr]
node_body = P.sepBy1 expr expr_break
    
node :: Parser T.Rval
node = P.between (P.char '{' >> spaces) (spaces >> P.char '}') node_body >>= return . T.Node

-- | Parse an application
application :: Parser T.Rval
application =
  do{ x <- rhs
    ; y <- P.between (P.char '(' >> spaces) (spaces >> P.char ')') rhs
    ; return $ T.App x y
    }

-- | Parse a top-level sequence of expressions
program :: Parser [T.Expr]
program = P.between spaces spaces node_body


