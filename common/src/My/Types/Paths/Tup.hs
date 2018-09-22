{-# LANGUAGE TypeFamilies #-}
module My.Types.Paths.Tup
  ( module My.Types.Paths.Tup
  , module My.Types.Paths.Path
  )
  where
  
import qualified My.Types.Syntax.Class as S
import My.Types.Paths.Path
import qualified Data.Map as M



-- | Generic constructor for a tuple
newtype Tup k a = Tup { getTup :: M.Map k (Node k [a] a) }
  
instance (S.Self k, S.Self a) => S.Self (Tup k a) where
  self_ n = pun (S.self_ n)
instance (S.Self k, S.Local a) => S.Local (Tup k a) where
  local_ n = pun (S.local_ n)

instance (S.Self k, S.Field a) => S.Field (Tup k a) where
  type Compound (Tup k a) = Pun (Path (Node k [a])) (S.Compound a)
  p #. n = pun (p S.#. n)

instance S.Self k => S.Assoc (Tup k a) where
  type Label (Tup k a) = Path (Node k [a])
  type Value (Tup k a) = a
  Path n f #: a =
    (Tup . M.singleton (S.self_ n) . f) (pure a)
  
-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun p a = Pun p a

pun :: S.Assoc s => Pun (S.Label s) (S.Value s) -> s
pun (Pun p a) = p S.#: a

instance (S.Self p, S.Self a) => S.Self (Pun p a) where self_ n = Pun (S.self_ n) (S.self_ n)
instance (S.Self p, S.Local a) => S.Local (Pun p a) where
  local_ n = Pun (S.self_ n) (S.local_ n)

instance (S.Field p, S.Field a) => S.Field (Pun p a) where
  type Compound (Pun p a) = Pun (S.Compound p) (S.Compound a)
  Pun p a #. n = Pun (p S.#. n) (a S.#. n)
  