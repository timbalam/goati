module Test.Eval
  ( evalTest
  , tests
  ) where

import Eval
  ( evalRval
  )
import Types.Eval
  ( emptyEnvF
  , emptyVtable
  , liftIO
  , runIOExcept
  , Value(..)
  , runEval
  , selfSymbol
  )
import qualified Types.Parser as T 
import qualified Error as E 
  
import Test.HUnit
  ( Test(..)
  , assertEqual
  , assertFailure
  , assertBool
  )

evalTest :: T.Rval -> Value -> Test
evalTest r expected =
  TestCase $
    runIOExcept
      (do{ res <- runEval (evalRval r) emptyEnvF emptyVtable emptyVtable
         ; liftIO $ assertEqual msg expected res
         })
      (assertFailure . ((msg ++ "\n") ++) . show)
  where
    ref = T.Ref . T.Ident
    msg = "Evaluatiing \"" ++ show r ++ "\""

    
errorTest :: String -> T.Rval -> (E.Error -> Bool) -> Test
errorTest msg r test =
  TestCase $
    runIOExcept
      (do{ res <- runEval (evalRval r) emptyEnvF emptyVtable emptyVtable
         ; liftIO $ assertFailure (msg' ++ "\nexpected: " ++ msg ++ "\n but got: " ++ show res)
         })
      (assertBool ("Evaluating \"" ++ show r ++ "\"") . test)
  where
    msg' = "Evaluating \"" ++ show r ++ "\"" 


isUnboundVar :: E.Error -> Bool
isUnboundVar (E.UnboundVar _ _) = True
isUnboundVar _ = False    
    
tests =
  TestList
    [ TestLabel "add" $
        evalTest
          (T.Number 1 `add` T.Number 1)
          (Number 2)
    , TestLabel "subtract" $
        evalTest
          (T.Number 1 `sub` T.Number 2)
          (Number (-1))
    , TestLabel "private variables" $ 
        errorTest
          "Unbound var '.priv'"
          (T.Rroute (T.Rnode [lident "priv" `T.Assign` T.Number 1] `T.Route` ref "priv"))
          isUnboundVar
    , TestLabel "public variables" $
        evalTest
          (T.Rroute (T.Rnode [lroute (T.Atom (ref "pub")) `T.Assign` T.Number 1] `T.Route` ref "pub"))
          (Number 1)
    , TestLabel "private variable access" $
        evalTest
          (T.Rroute 
            (T.Rnode
              [ lroute (T.Atom (ref "pub")) `T.Assign` rident "priv"
              , lident "priv" `T.Assign` T.Number 1
              ]
            `T.Route` ref "pub"))
          (Number 1)
    , TestLabel "object keys" $
        evalTest
          (T.Rroute
            (T.Rnode
              [ lroute (T.Atom (T.Key (T.Number 1))) `T.Assign` T.String "one"]
            `T.Route` T.Key (T.Number 1)))
          (String "one")
    , TestLabel "undefined variables" $
        errorTest
          "Unbound var '.c'"
          (T.Rroute
            (T.Rnode 
              [ lroute (T.Atom (ref "a")) `T.Assign` T.Number 2
              , lroute (T.Atom (ref "b")) `T.Assign` (rident "c" `add` T.Number 1)
              ]
            `T.Route` ref "b"))
          isUnboundVar
    , TestLabel "application  overriding public variables" $
        evalTest 
          (T.Rroute 
            ((T.Rnode 
              [ lroute (T.Atom (ref "a")) `T.Assign` T.Number 2
              , lroute (T.Atom (ref "b")) `T.Assign` (T.Rroute (T.Atom (ref "a")) `add` T.Number 1)
              ]
            `T.App` 
              T.Rnode
                [lroute (T.Atom (ref "a")) `T.Assign` T.Number 1])
            `T.Route` ref "b"))
          (Number 2)
    , TestLabel "Default definition" $
        evalTest
          (T.Rroute
            ((T.Rnode
              [ lroute (T.Atom (ref "a")) `T.Assign` (rident "b" `sub` T.Number 1)
              , lroute (T.Atom (ref "b")) `T.Assign` (rident "a" `add` T.Number 1)
              ]
            `T.App`
              T.Rnode
                [ lroute (T.Atom (ref "b")) `T.Assign` T.Number 2])
            `T.Route` ref "a"))
          (Number 1)
    , TestLabel "Route getter" $
        evalTest
          (T.Rroute
            (T.Rroute
              (T.Rnode
                [ lroute (T.Atom (ref "a"))
                  `T.Assign`
                    T.Rnode
                      [ lroute (T.Atom (ref "aa")) `T.Assign` T.Number 2
                      ]
                ]
              `T.Route` ref "a")
            `T.Route` ref "aa"))
          (Number 2)
    , TestLabel "Route setter" $
        evalTest
          (T.Rroute
            (T.Rroute
              (T.Rnode
                [ lroute (T.Lroute (T.Atom (ref "a")) `T.Route` (ref "aa"))
                  `T.Assign` T.Number 2
                ]
              `T.Route` ref "a")
            `T.Route` ref "aa"))
          (Number 2)
    ]
  where
    ref = T.Ref . T.Ident
    lident = T.Laddress . T.Lident . T.Ident
    lroute = T.Laddress . T.Lroute
    rident = T.Rident . T.Ident
    add = T.Binop T.Add
    sub = T.Binop T.Sub