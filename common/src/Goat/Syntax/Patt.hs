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
newtype Patt stmt ext lcmp lhs cmp pun a =
  Patt
    (ExtendBlock
      (Pun lcmp lhs (Patt stmt ext lcmp lhs cmp a) cmp pun)
      ext
      (Path a))

type Patt_ p =
  ( Path_ p, ExtendBlock_ p, Pun_ (Stmt p), Rhs (Stmt p) ~ p )
  -- p, Compound p, Stmt p, Ext p, Lhs (Stmt p), Rhs (Stmt p), Compound (Lhs (Stmt p))