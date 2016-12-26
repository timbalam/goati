module Test.Eval
  ( assertEval
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
  , Assertion
  , assertEqual
  , assertFailure
  , assertBool
  )

assertEval :: T.Rval -> Value -> Assertion
assertEval r expected =
  runIOExcept
    (do{ res <- runEval (evalRval r) emptyEnvF emptyVtable emptyVtable
       ; liftIO $ assertEqual msg expected res
       })
    (assertFailure . ((msg ++ "\n") ++) . show)
  where
    ref = T.Ref . T.Ident
    msg = "Evaluatiing \"" ++ show r ++ "\""

    
assertError :: String -> T.Rval -> (E.Error -> Bool) -> Assertion
assertError msg r test =
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
    [ TestLabel "add" . TestCase $
        assertEval
          (T.Number 1 `add` T.Number 1)
          (Number 2)
    , TestLabel "subtract" . TestCase $
        assertEval
          (T.Number 1 `sub` T.Number 2)
          (Number (-1))
    , TestLabel "private variables" . TestCase $ 
        assertError
          "Unbound var '.priv'"
          (T.Rnode [lident "priv" `T.Assign` T.Number 1] `rref` "priv")
          isUnboundVar
    , TestLabel "public variables" . TestCase $
        assertEval
          (T.Rnode [lsref "pub" `T.Assign` T.Number 1] `rref` "pub")
          (Number 1)
    , TestLabel "private variable access" . TestCase $
        assertEval
          (T.Rnode
            [ lsref "pub" `T.Assign` rident "priv"
            , lident "priv" `T.Assign` T.Number 1
            ]
          `rref` "pub")
          (Number 1)
    , TestLabel "object keys" . TestCase $
        assertEval
          (T.Rnode [lskey (T.Number 1) `T.Assign` T.String "one"] `rkey` T.Number 1)
          (String "one")
    , TestLabel "undefined variables" . TestCase $
        assertError
          "Unbound var '.c'"
          (T.Rnode 
            [ lsref "a" `T.Assign` T.Number 2
            , lsref "b" `T.Assign` (rident "c" `add` T.Number 1)
            ]
          `rref` "b")
          isUnboundVar
    , TestLabel "application  overriding public variables" . TestCase $
        assertEval
          ((T.Rnode 
            [ lsref "a" `T.Assign` T.Number 2
            , lsref "b" `T.Assign` (rsref "a" `add` T.Number 1)
            ]
          `T.App` T.Rnode [lsref "a" `T.Assign` T.Number 1])
          `rref` "b")
          (Number 2)
    , TestLabel "Default definition" . TestCase $
        assertEval
          ((T.Rnode
            [ lsref "a" `T.Assign` (rident "b" `sub` T.Number 1)
            , lsref "b" `T.Assign` (rident "a" `add` T.Number 1)
            ]
          `T.App` T.Rnode [ lsref "b" `T.Assign` T.Number 2])
          `rref` "a")
          (Number 1)
    , TestLabel "Route getter" . TestCase $
        assertEval
          ((T.Rnode
            [ lsref "a" 
              `T.Assign`
                T.Rnode [ lsref "aa" `T.Assign` T.Number 2 ]
            ]
          `rref` "a")
          `rref` "aa")
          (Number 2)
    , TestLabel "Route setter" . TestCase $
        assertEval
          ((T.Rnode
            [ (lsref' "a" `lref` "aa")
              `T.Assign` T.Number 2
            ]
          `rref` "a")
          `rref` "aa")
          (Number 2)
    , TestLabel "public members in scope" . TestCase $
        assertEval
          (T.Rnode
            [ lsref "a" `T.Assign` T.Number 1
            , lsref "b" `T.Assign` rident "a"
            ]
          `rref` "b")
          (Number 1)
    , TestLabel "application overriding nested property" . TestCase $
        assertEval
          ((T.Rnode
            [ lsref "a" `T.Assign` T.Rnode [lsref "aa" `T.Assign` T.Number 0]
            , lsref "b" `T.Assign` (rident "a" `rref` "aa")
            ]
          `T.App`
            T.Rnode [(lsref' "a" `lref` "aa") `T.Assign` T.Number 1])
          `rref` "b")
          (Number 1)
    , TestLabel "shadowing update" . TestCase $
        assertEval
          ((T.Rnode
            [ lident "outer" `T.Assign` T.Rnode [lsref "a" `T.Assign` T.Number 1]
            , lsref "inner"
              `T.Assign`
                T.Rnode
                  [ (lident' "outer" `lref` "b") `T.Assign` T.Number 2
                  , lsref "ab"
                    `T.Assign` 
                      ((rident "outer" `rref` "a") `add` (rident "outer" `rref` "b"))
                  ]
            ]
            `rref` "inner")
            `rref` "ab")
          (Number 3)
    , TestLabel "shadowing update 2" . TestCase $
        assertEval
          (T.Rnode
            [ lident "outer"
              `T.Assign`
                T.Rnode
                  [ lsref "a" `T.Assign` T.Number 2
                  , lsref "b" `T.Assign` T.Number 1
                  ]
            , lsref "inner"
              `T.Assign` T.Rnode [(lsref' "outer" `lref` "b") `T.Assign` T.Number 2]
            , lsref "ab"
              `T.Assign`
                 ((rident "outer" `rref` "a") `add` (rident "outer" `rref` "b"))
            ]
          `rref` "ab")
          (Number 3)
    , TestLabel "destructuring" . TestCase $
        let
          rnode = 
            T.Rnode
              [ lident "obj"
                `T.Assign`
                  T.Rnode
                    [ lsref "a" `T.Assign` T.Number 2
                    , lsref "b" `T.Assign` T.Number 3
                    ]
              , T.Lnode
                  [ plainsref "a" `T.ReversibleAssign` lsref "da"
                  , plainsref "b" `T.ReversibleAssign` lsref "db"
                  ]
                `T.Assign` rident "obj"
              ]
        in
          do{ assertEval
                (rnode `rref` "da")
                (Number 2)
            ; assertEval
                (rnode `rref` "db")
                (Number 3)
            }
    , TestLabel "destructuring unpack" . TestCase $
        assertEval
          ((T.Rnode
            [ lident "obj"
              `T.Assign`
                T.Rnode
                  [ lsref "a" `T.Assign` T.Number 2
                  , lsref "b" `T.Assign` T.Number 3
                  ]
            , T.Lnode
                [ plainsref "a" `T.ReversibleAssign` lsref "da"
                , T.ReversibleUnpack $ lsref "dobj"
                ]
              `T.Assign` rident "obj"
            ]
          `rref` "dobj")
          `rref` "b")
          (Number 3)
    , TestLabel "nested destructuring" . TestCase $
        assertEval
          (T.Rnode
            [ lident "y1"
              `T.Assign`
                T.Rnode
                  [ lsref "a"
                    `T.Assign`
                      T.Rnode
                        [ lsref "aa" `T.Assign` T.Number 3
                        , lsref "ab" `T.Assign` T.Rnode [lsref "aba" `T.Assign` T.Number 4]
                        ]
                  ]
            , T.Lnode
                [ (plainsref "a" `plainref` "aa") `T.ReversibleAssign` lsref "da"
                , ((plainsref "a" `plainref` "ab") `plainref` "aba") `T.ReversibleAssign` lsref "daba"
                ]
              `T.Assign` rident "y1"
            ]
          `rref` "daba")
          (Number 4)
    , TestLabel "unpack" . TestCase $
        assertEval
          ((T.Rnode
            [ lident "w1" `T.Assign` T.Rnode [lsref "a" `T.Assign` T.Number 1]
            , lsref "w2"
              `T.Assign`
                T.Rnode
                  [ lsref "b" `T.Assign` rident "a"
                  , T.Unpack $ rident "w1"
                  ]
            ]
          `rref` "w2")
          `rref` "b")
          (Number 1)
    ]
  where
    lident' = T.Lident . T.Ident
    lsref' = T.Lroute . T.Atom . T.Ref . T.Ident
    lskey' = T.Lroute . T.Atom . T.Key
    lref' x y = T.Lroute (x `T.Route` T.Ref (T.Ident y))
    lkey' x y = T.Lroute (x `T.Route` T.Key y)
    lident = T.Laddress . lident'
    lsref = T.Laddress . lsref'
    lskey = T.Laddress . lskey'
    lref x y = T.Laddress (x `lref'` y)
    lkey x y = T.Laddress (x `lkey'` y)
    rident = T.Rident . T.Ident
    rsref = T.Rroute . T.Atom . T.Ref . T.Ident
    rskey = T.Rroute . T.Atom . T.Key
    rref x y = T.Rroute (x `T.Route` T.Ref (T.Ident y))
    rkey x y = T.Rroute (x `T.Route` T.Key y)
    plainsref = T.PlainRoute . T.Atom . T.Ref . T.Ident
    plainskey = T.PlainRoute . T.Atom . T.Key
    plainref x y = T.PlainRoute (x `T.Route` T.Ref (T.Ident y))
    plainkey x y = T.PlainRoute (x `T.Route` T.Key y)
    add = T.Binop T.Add
    sub = T.Binop T.Sub