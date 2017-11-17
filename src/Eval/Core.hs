{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, OverloadedStrings, RecordWildCards #-}

module Eval.Core
where

import Types.Core

eval :: Expr a -> Maybe (Expr a)
eval x@(Number _) = Just x

eval x@(String _) = Just x

eval x@(Bool _) = Just x

eval (Var _) = Nothing

eval (Block m es) =
  do
    ms <- traverse self es
    let m' = M.unions (m:ms)
      
   
    

