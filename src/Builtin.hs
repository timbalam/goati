{-# LANGUAGE OverloadedStrings #-}
module Builtin
  ( numberSelf
  , boolSelf
  )
where

import Types.Expr
import qualified Data.Map as M
import Control.Monad.Trans
import Bound
      
numberSelf :: Double -> M.Map Tid (Node (Member a))
numberSelf d = M.fromList [
  (Label "neg", (Closed . Member . lift . Number) (-d)),
  (Label "add", nodeBuiltin (AddNumber d)),
  (Label "sub", nodeBuiltin (SubNumber d)),
  (Label "prod", nodeBuiltin (ProdNumber d)),
  (Label "div", nodeBuiltin (DivNumber d)),
  (Label "pow", nodeBuiltin (PowNumber d)),
  (Label "gt", nodeBuiltin (GtNumber d)),
  (Label "lt", nodeBuiltin (LtNumber d)),
  (Label "eq", nodeBuiltin (EqNumber d)),
  (Label "ne", nodeBuiltin (NeNumber d)),
  (Label "ge", nodeBuiltin (GeNumber d)),
  (Label "le", nodeBuiltin (LeNumber d))
  ]
  
  
boolSelf :: Bool -> M.Map Tid (Node (Member a))
boolSelf b = M.fromList [
  (Label "not", (Closed . Member . lift . Bool) (not b)),
  (Label "and", nodeBuiltin (AndBool b)),
  (Label "or", nodeBuiltin (OrBool b)),
  (Label "match", (Closed . Member . Scope . Var . B) (label b))
  ]
  where
    label True = Label "ifTrue"
    label False = Label "ifFalse"
  
 
  
nodeBuiltin :: Builtin -> Node (Member a)
nodeBuiltin op = (Closed . Member . lift . Block [] . M.fromList) [
  (Label "y", (Closed . lift . Member . Scope . 
    Builtin op . Var . B) (Label "x"))
  ]
  