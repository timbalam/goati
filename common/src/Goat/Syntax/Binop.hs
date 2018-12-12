module Binop
  where
  
infixr 8 #^
infixl 7 #*, #/
infixl 6 #+, #-
infix 4 #==, #!=, #<, #<=, #>=, #>

class Arith_ r where
  (#+) :: r -> r -> r
  (#-) :: r -> r -> r
  (#*) :: r -> r -> r
  (#/) :: r -> r -> r
  (#^) :: r -> r -> r
  
class Cmp_ r where
  (#==) :: r -> r -> r
  (#!=) :: r -> r -> r
  (#>) :: r -> r -> r
  (#<) :: r -> r -> r
  (#>=) :: r -> r -> r
  (#<=) :: r -> r -> r