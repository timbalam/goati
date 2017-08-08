module Types.Util.List
  where
  
infixr 2 :<:, :>:

data Suffix b a = b :>: [a]
  deriving Eq
  
  
data Prefix b a =
    [a] :<: b
  deriving Eq