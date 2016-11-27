module Test.Eval
  ( evalTest
  , tests
  ) where

import Eval
  ( evalRval
  , emptyNode
  , lensSelf
  , envLens
  )
import Types.Eval
  ( Value(..)
  , runEval
  , selfSymbol
  , getEnv
  , withEnv
  )
import qualified Types.Parser as T  
import Utils.Lens
  ( set
  )
  
import Test.HUnit
  ( Test(..)
  , assertEqual
  , assertFailure
  )

evalTest :: T.Rval -> Value -> Test
evalTest r expected =
  TestCase $
    do{ res <- runEval (do{ p <- set (envLens (ref "hi")) (return (Number 1)) (set lensSelf emptyNode getEnv); withEnv (const p) (evalRval r)}) []
      ; either
          (assertFailure . show)
          (assertEqual ("Evaluating \"" ++ show r ++ "\"") expected)
          res
      }
  where
    ref = T.Ref . T.Ident
tests =
  TestList
    [ evalTest (T.Number 1 `add` T.Number 1) $ Number 2
    , evalTest (T.Number 1 `sub` T.Number 2) $ Number (-1)
    , evalTest (T.Rroute (T.Rnode [lroute (T.Atom (ref "pub")) `T.Assign` T.Number 1] `T.Route` ref "pub")) $ Number 1
    , evalTest (T.Rroute (T.Rnode [lroute (T.Atom (ref "pub")) `T.Assign` rident "priv", lident "priv" `T.Assign` T.Number 1] `T.Route` ref "pub")) $ Number 1
    , evalTest (T.Rroute (T.Rnode [lroute (T.Atom (T.Key (T.Number 1))) `T.Assign` T.String "one"] `T.Route` T.Key (T.Number 1))) $ String "one"
    , evalTest (T.Rroute ((T.Rnode [lroute (T.Atom (ref "a")) `T.Assign` T.Number 2, lroute (T.Atom (ref "b")) `T.Assign` (rident "a" `add` T.Number 1)] `T.App` T.Rnode [lroute (T.Atom (ref "a")) `T.Assign` T.Number 1]) `T.Route` ref "b")) $ Number 2
    --, evalTest (T.Rroute ((T.Rnode [lroute (T.Atom (ref "a")) `T.Assign` (rident "b" `sub` T.Number 1), lroute (T.Atom (ref "b")) `T.Assign` (rident "a" `add` T.Number 1)] `T.App` T.Rnode [lroute (T.Atom (ref "b")) `T.Assign` T.Number 2]) `T.Route` ref "a")) $ Number 1
    ]
  where
    ref = T.Ref . T.Ident
    lident = T.Laddress . T.Lident . T.Ident
    lroute = T.Laddress . T.Lroute
    rident = T.Rident . T.Ident
    add = T.Binop T.Add
    sub = T.Binop T.Sub