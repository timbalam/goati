module Utils.List.Prefix
  where
  
infixr 5 >:, :>


data Suffix b a =
    b >: [a]
  deriving Eq
  
  
data Prefix b a =
    [a] :> b
  deriving Eq