module Goat.Syntax.Patt 
  where
  
import Goat.Syntax.Field (Field_(..), Path_)
import Goat.Syntax.Block (Block_(..), Extend_(..), ExtendBlock_)


-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
-- * Let path pattern (leaf pattern assigns matched value to path)
-- * Block pattern (matches a set of paths to nested (lifted) patterns)
-- * An block pattern with left over pattern (matches set of fields not
--   matched by the block pattern)
type Patt_ p =
  ( Path_ p, ExtendBlock_ p
  , Pun (Stmt p), LetMatch (Stmt p)
  , Lower (Rhs (Stmt p)) ~ p
  )