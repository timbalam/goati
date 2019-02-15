module Goat.Syntax.Expr
  where
  
  
type Lit r =
  ( Text_ r, Fractional r, IsString r, Extern r, Block r )
  
parseLit :: Lit_ r => Parser (Stmt r) -> Parser r
parseLit ps =
  parseText                     -- '"' ...
    <|> parseNumber             -- digit ...
    <|> (parseIdent <* spaces)  -- alpha ...
    <|> parseExtern             -- '@' ...
    -- <|> (esc <*> first)      -- '^' ...
    -- <|> parens p             -- '(' ...
    <|> parseBlock ps           -- '{' ... 
  
newtype SomeLit stmt =
  SomeLit {
    getLit
     :: forall t a
      . Comp 
          (Text <:
          Number <:
          Ident <:
          Extern <:
          Block stmt <:
          t)
          a
    }
  deriving (Text_, Fractional, IsString, Extern_)

instance Block_ (SomeLit stmt) where
  type Stmt (SomeLit stmt) = stmt
  block_ bdy = SomeLit (block_ bdy)

showLit
 :: (stmt -> ShowS) -> SomeLit stmt -> Comp t ShowS
showLit ss =
  showBlock ss
    . showExtern
    . showIdent
    . showNumber
    . showText
    . getLit

fromLit
 :: Lit_ r => (stmt -> Stmt r) -> SomeLit stmt -> Comp t r
fromLit ks =
  fromBlock ks
    . fromExtern
    . fromIdent
    . fromNumber
    . fromText
    . getLit

litProof :: SomeLit s -> SomeLit s
litProof = run . fromLit

-- | Expression with operator precedence
type Op_ r =
  ( LogicB_ r, ArithB_ r, CmpB_ r, Unop_ r )
  
parseOp
 :: Op_ r => Parser r -> Parser r
parseOp p =
  parseLogicB
    (parseCmpB
      (parseArithB
        (parseUnop <*> (p <|> parens (parseOp p)))))

newtype SomeOp =
  SomeOp {
    getOp
     :: forall t a 
      . Comp (LogicB <: CmpB <: ArithB <: Unop <: t) a
    }

instance LogicB_ SomeOp where
  SomeOp a #|| SomeOp b = SomeOp (a #|| b)
  SomeOp a #&& SomeOp b = SomeOp (a #&& b)
    
instance CmpB_ SomeOp where
  SomeOp a #== SomeOp b = SomeOp (a #== b)
  SomeOp a #!= SomeOp b = SomeOp (a #!= b)
  SomeOp a #<  SomeOp b = SomeOp (a #<  b)
  SomeOp a #<= SomeOp b = SomeOp (a #<= b)
  SomeOp a #>  SomeOp b = SomeOp (a #>  b)
  SomeOp a #>= SomeOp b = SomeOp (a #>= b)

instance ArithB_ SomeOp where
  SomeOp a #+ SomeOp b = SomeOp (a #+ b)
  SomeOp a #- SomeOp b = SomeOp (a #- b)
  SomeOp a #* SomeOp b = SomeOp (a #* b)
  SomeOp a #/ SomeOp b = SomeOp (a #/ b)
  SomeOp a #^ SomeOp b = SomeOp (a #^ b)

instance Unop SomeOp where
  neg_ (SomeOp a) = SomeOp (neg_ a)
  not_ (SomeOp a) = SomeOp (not_ a)

showOp :: SomeOp -> Comp t ShowS
showOp =
  showCmpB
    . showArithB
    . showLogicB
    . getOp


-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form.
type PathExpr r =
  ( Chain_ r
  , Text_ r, Fractional r
  --, LogicB_ r, ArithB_ r, CmpB_ r
  --, Unop_ r
  --, Esc r, Lower r ~ r
  --, Local r, Self r
  , IsString r
  , Extern r
  , ExtendBlock r
  )
  -- r, Compound r, Stmt r, Ext r

-- | Parse a chain of field accesses and extensions
parsePathExpr
 :: PathExpr r => Parser (Stmt r) -> Parser r
parsePathExpr ps =
  first <**> rest
  where
    rest = go id where 
      go k = (do
        k' <- step 
        go (k' . k))
        <|> return k
    
    step = (do
      ext <- parseExtend
      b <- parseBlock ps
      return (`ext` b))     -- '{' ...
        <|> parseField      -- '.' ...
    
    first =
      parseText                     -- '"' ...
        <|> parseNumber             -- digit ...
        <|> (parseIdent <* spaces)  -- alpha ...
        <|> (do 
          x <- parseSelf
          f <- parseField
          return (f x))             -- '.' alpha ...
        <|> parseExtern             -- '@' ...
        -- <|> (esc <*> first)      -- '^' ...
        -- <|> parens p             -- '(' ...
        <|> parseBlock ps           -- '{' ...  
        

newtype SomePathExpr stmt where
  SomePathExpr {
    getPathExpr
     :: forall t a
      . Comp
          (Field SomePathExpr
    }
