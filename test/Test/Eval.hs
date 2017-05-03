module Test.Eval
  ( assertEval
  , tests
  ) where

import Control.Monad.IO.Class( liftIO )
import Control.Monad.Except ( runExceptT )
import Eval
  ( evalRval
  )
import Types.Eval
import qualified Types.Parser as T
import Types.Short
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
  do{ e <- (runExceptT . runIded . runESRT . evalRval) r
    ; either (assertFailure . ((banner ++ "\n") ++) . show) (assertEqual banner expected) e
    }
  where
    ref = T.Ref . T.Ident
    banner = "Evaluatiing \"" ++ show r ++ "\""

    
assertError :: String -> T.Rval -> (E.Error -> Bool) -> Assertion
assertError msg r test =
  do{ e <- (runExceptT . runIded . runESRT . evalRval) r
    ; either (assertBool banner . test) (assertFailure . ((banner ++ "\nexpected: " ++ msg ++ "\n but got: ") ++) . show) e
    }
  where
    banner = "Evaluating \"" ++ show r ++ "\"" 


isUnboundVar :: E.Error -> Bool
isUnboundVar (E.UnboundVar _ _) = True
isUnboundVar _ = False
    
tests =
  TestList
    [ TestLabel "add" . TestCase $
        assertEval
          (T.Number 1 `_add_` T.Number 1)
          (Number 2)
    , TestLabel "subtract" . TestCase $
        assertEval
          (T.Number 1 `_sub_` T.Number 2)
          (Number (-1))
    , TestLabel "public variable" . TestCase $
        assertEval
          (T.Rnode [lsref "pub" `T.Assign` T.Number 1] `rref` "pub")
          (Number 1)
    , TestLabel "private variable" . TestCase $ 
        assertError
          "Unbound var '.priv'"
          (T.Rnode [lident "priv" `T.Assign` T.Number 1] `rref` "priv")
          isUnboundVar
    , TestLabel "private variable access backward" . TestCase $
        assertEval
          (T.Rnode
            [ lident "priv" `T.Assign` T.Number 1
            , lsref "pub" `T.Assign` rident "priv"
            ]
          `rref` "pub")
          (Number 1)
    , TestLabel "private variable access forward" . TestCase $
        assertEval
          (T.Rnode
            [ lsref "pub" `T.Assign` rident "priv"
            , lident "priv" `T.Assign` T.Number 1
            ]
          `rref` "pub")
          (Number 1)
    , TestLabel "private access of public variable ##unimplemented" . TestCase $
        assertEval
          (T.Rnode
            [ lsref "a" `T.Assign` T.Number 1
            , lsref "b" `T.Assign` rident "a"
            ]
          `rref` "b")
          (Number 1)
    , TestLabel "access backward public variable from same scope" . TestCase $
        assertEval
          (T.Rnode
            [ lsref "b" `T.Assign` T.Number 2
            , lsref "a" `T.Assign` rsref "b" 
            ]
          `rref` "a")
          (Number 2)
    , TestLabel "access forward public variable from same scope" . TestCase $
        assertEval
          (T.Rnode
            [ lsref "a" `T.Assign` rsref "b"
            , lsref "b" `T.Assign` T.Number 2
            ]
          `rref` "a")
          (Number 2)
    , TestLabel "value key" . TestCase $
        assertEval
          (T.Rnode [lskey (T.Number 1) `T.Assign` T.String "one"] `rkey` T.Number 1)
          (String "one")
    , TestLabel "self referencing key ##depreciated behaviour" . TestCase $
        assertEval
          (T.Rnode
            [ lident "object"
              `T.Assign`
                T.Rnode
                  [ lsref "key" `T.Assign` T.Rnode []
                  , lskey (rsref "key") `T.Assign` T.String "one"
                  ]
            , lsref "a"
              `T.Assign`
                (rident "object" `rkey` (rident "object" `rref` "key"))
            ]
          `rref` "a")
          (String "one")
    , TestLabel "env referencing key" . TestCase $
        assertEval
          (T.Rnode
            [ lident "object"
              `T.Assign`
                T.Rnode [ lskey (rident "key") `T.Assign` T.String "one" ]
            , lident "key" `T.Assign` T.Number 1
            , lsref "a"
              `T.Assign`
                (rident "object" `rkey` rident "key")
            ]
          `rref` "a")
          (String "one")
    , TestLabel "node key" . TestCase $
        assertEval
          (T.Rnode
            [ lident "object" `T.Assign` T.Rnode [lsref "key" `T.Assign` T.Number 1]
            , lident "another"
                `T.Assign`
                  T.Rnode [ lskey (rident "object") `T.Assign` T.String "object" ]
            , lsref "a"
                `T.Assign`
                  (rident "another" `rkey` rident "object")
            ]
          `rref` "a")
          (String "object")
    , TestLabel "unbound variable" . TestCase $
        assertError
          "Unbound var '.c'"
          (T.Rnode 
            [ lsref "a" `T.Assign` T.Number 2
            , lsref "b" `T.Assign` (rident "c" `_add_` T.Number 1)
            ]
          `rref` "b")
          isUnboundVar
    , TestLabel "undefined variable" . TestCase $
        let node = 
              T.Rnode
                  [ T.Declare (lsref' "a")
                  , lsref "b" `T.Assign` T.Number 1
                  ]
        in
          do{ assertEval (node `rref` "b") (Number 1)
            ; assertError "Unbound var '.a'" (node `rref` "a") isUnboundVar
            }
    , TestLabel "unset variable forwards" . TestCase $
        assertError
          "Unbound var '.c'"
          (T.Rnode
            [ lident "c" `T.Assign` T.Number 1
            , lident "b"
              `T.Assign`
                T.Rnode
                  [ T.Declare (lident' "c")
                  , lsref "a" `T.Assign` rident "c"
                  ]
            , lsref "ba" `T.Assign` (rident "b" `rref` "a")
            ]
          `rref` "ba")
          isUnboundVar
    , TestLabel "unset variable backwards" . TestCase $
        assertError
          "Unbound var '.c'"
          (T.Rnode
            [ lident "c" `T.Assign` T.Number 1
            , lident "b"
              `T.Assign`
                T.Rnode
                  [ lsref "a" `T.Assign` rident "c"
                  , T.Declare (lident' "c")
                  ]
            , lsref "ba" `T.Assign` (rident "b" `rref` "a")
            ]
          `rref` "ba")
          isUnboundVar
    , TestLabel "undefined key" . TestCase $
        let node = 
              T.Rnode
                  [ lident "a1" `T.Assign` T.Rnode []
                  , lident "b1" `T.Assign` T.Rnode []
                  , lident "object"
                    `T.Assign` 
                      T.Rnode
                        [ lskey (rident "a1") `T.Assign` T.String "exists"
                        ]
                  , lsref "a2" `T.Assign` (rident "object" `rkey` (rident "a1"))
                  , lsref "b2" `T.Assign` (rident "object" `rkey` (rident "b1"))
                  ]
        in
          do{ assertEval (node `rref` "a2") (String "exists")
            ; assertError "Unbound key 'object.b1'" (node `rref` "b2") isUnboundVar
            }
    , TestLabel "application  overriding public variable" . TestCase $
        assertEval
          ((T.Rnode 
            [ lsref "a" `T.Assign` T.Number 2
            , lsref "b" `T.Assign` (rsref "a" `_add_` T.Number 1)
            ]
          `T.App` T.Rnode [lsref "a" `T.Assign` T.Number 1])
          `rref` "b")
          (Number 2)
    , TestLabel "default definition forward" . TestCase $
        assertEval
          ((T.Rnode
            [ lsref "a" `T.Assign` (rsref "b" `_sub_` T.Number 1)
            , lsref "b" `T.Assign` (rsref "a" `_add_` T.Number 1)
            ]
          `T.App` T.Rnode [ lsref "b" `T.Assign` T.Number 2])
          `rref` "a")
          (Number 1)
    , TestLabel "default definition backward" . TestCase $
        assertEval
          ((T.Rnode
            [ lsref "a" `T.Assign` (rsref "b" `_sub_` T.Number 1)
            , lsref "b" `T.Assign` (rsref "a" `_add_` T.Number 1)
            ]
          `T.App` T.Rnode [ lsref "a" `T.Assign` T.Number 2])
          `rref` "b")
          (Number 3)
    , TestLabel "route getter" . TestCase $
        assertEval
          ((T.Rnode
            [ lsref "a" 
              `T.Assign`
                T.Rnode [ lsref "aa" `T.Assign` T.Number 2 ]
            ]
          `rref` "a")
          `rref` "aa")
          (Number 2)
    , TestLabel "route setter" . TestCase $
        assertEval
          ((T.Rnode
            [ (lsref' "a" `lref` "aa")
              `T.Assign` T.Number 2
            ]
          `rref` "a")
          `rref` "aa")
          (Number 2)
    , TestLabel "application overriding nested property" . TestCase $
        assertEval
          ((T.Rnode
            [ lsref "a" `T.Assign` T.Rnode [lsref "aa" `T.Assign` T.Number 0]
            , lsref "b" `T.Assign` (rsref "a" `rref` "aa")
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
                      ((rident "outer" `rref` "a") `_add_` (rident "outer" `rref` "b"))
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
                 ((rident "outer" `rref` "a") `_add_` (rident "outer" `rref` "b"))
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
          do{ assertEval (rnode `rref` "da") (Number 2)
            ; assertEval (rnode `rref` "db") (Number 3)
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
                , T.ReversibleUnpack (lsref "dobj")
                ]
              `T.Assign` rident "obj"
            ]
          `rref` "dobj")
          `rref` "b")
          (Number 3)
    , TestLabel "nested destructuring" . TestCase $
        let 
          rnode =
            T.Rnode
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
              , lsref "raba"
                  `T.Assign`
                    (((rident "y1" `rref` "a") `rref` "ab") `rref` "aba")
              ]
        in
          do{ assertEval (rnode `rref` "raba") (Number 4)
            ; assertEval (rnode `rref` "daba") (Number 4)
            }
    , TestLabel "unpack visible publicly" . TestCase $
        let
          rnode =
            T.Rnode
              [ lident "w1" `T.Assign` T.Rnode [lsref "a" `T.Assign` T.Number 1]
              , lsref "w2"
                `T.Assign`
                  T.Rnode
                    [ lsref "b" `T.Assign` rsref "a"
                    , T.Unpack (rident "w1")
                    ]
              , lsref "w3" `T.Assign` (rsref "w2" `rref` "a")
              ]
        in
          do{ assertEval ((rnode `rref` "w2") `rref` "b") (Number 1)
            ; assertEval (rnode `rref` "w3") (Number 1)
            }
    , TestLabel "unpack visible privately ##unimplemented" . TestCase $
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
    , TestLabel "parent scope binding" . TestCase $
        assertEval
          ((T.Rnode
            [ lsref "inner" `T.Assign` T.Number 1
            , lident "parInner" `T.Assign` rsref "inner"
            , lsref "outer"
              `T.Assign`
                T.Rnode
                  [ lsref "inner" `T.Assign` T.Number 2
                  , lsref "a" `T.Assign` rident "parInner"
                  ]
            ]
          `rref` "outer")
          `rref` "a")
          (Number 1)
    , TestLabel "unpack scope binding" . TestCase $
        assertEval
          (T.Rnode
            [ lident "inner"
              `T.Assign`
                T.Rnode
                  [ lsref "var" `T.Assign` T.Number 1
                  , lsref "innerVar" `T.Assign` rsref "var"
                  ]
            , lsref "var" `T.Assign` T.Number 2
            , T.Unpack (rident "inner")
            ]
          `rref` "innerVar")
          (Number 1)
    , TestLabel "self referencing definition" . TestCase $
        assertEval
          (T.Rnode
            [ lident "y"
              `T.Assign`
                T.Rnode
                  [ lsref "a" `T.Assign` (rident "y" `rref` "b")
                  , lsref "b" `T.Assign` T.Number 1
                  ]
            , lsref "z" `T.Assign` (rident "y" `rref` "a")
            ]
          `rref` "z")
          (Number 1)
    ]