module Types
  ( Ident(..)
  , Name(..)
  , LocalRoute(..)
  , Route(..)
  , Lval(..)
  , Unexpr(..)
  , Rval(..)
  , Expr(..)
  )
where

-- | My-language identifiers
newtype Ident = Ident String

class Show Ident where
  show (Ident s) = show $ "\"" ++ escape s ++ "\""
    where
      escape = foldr  ((++) . escapeChar) ""
      escapeChar '\\' = "\\\\"
      escapeChar '"' = "\\\""
      escapeChar '\n' = "\\n"
      escapeChar '\r' = "\\r"
      escapeChar '\t' = "\\t"
      escapeChar x = x
       

data Name = Ref Ident | Key Rval
newtype LocalRoute = LocalRoute [Name]
data Route = Absolute Ident LocalRoute | Local LocalRoute

-- | My-language lval
data Lval = Lroute Route | Unnode [Unexpr]
data Unexpr = Unassign LocalRoute Lval | Pack Lval

-- | My language rval
data Rval = Number Double | String String | Rroute Route | Node [Expr] | App Rval Rval
data Expr = Assign Lval Rval | Eval Rval | Unpack Rval

