module Test.Eval
  ( assertEval
  , tests
  ) where

import Control.Monad.IO.Class( liftIO )
import Control.Monad.Reader ( runReaderT )
import Control.Exception

import Eval
  ( evalRval
  , runEval
  )
import Types.Eval
import qualified Types.Parser as T
import Types.Parser.Short
import qualified Types.Error as E
  
import Test.HUnit
  ( Test(..)
  , Assertion
  , assertEqual
  , assertFailure
  , assertBool
  )
  
assertEval :: T.Rval -> Value -> Assertion
assertEval r expected =
  do{ primEnv <- primitiveBindings
    ; v <- runEval (evalRval r) (primEnv, emptyEnv)
    ; assertEqual banner expected v
    } 
  where
    ref = T.Ident
    banner = "Evaluatiing \"" ++ show r ++ "\""

    
assertError :: Exception e => String -> T.Rval -> (e -> Bool) -> Assertion
assertError msg r test =
  catch
    (do{ primEnv <- primitiveBindings
       ; v <- runEval (evalRval r) (primEnv, emptyEnv)
       ; assertFailure (banner ++ "\nexpected: " ++ msg ++ "\n but got: " ++ show v)
       })
    (\ e -> if test e then return () else assertFailure (banner ++ "\nexpected: " ++ msg ++ "\n but got: " ++ show e))
  where
    banner = "Evaluating \"" ++ show r ++ "\"" 

isUnboundVar :: String -> E.UnboundVar T.Ident -> Bool
isUnboundVar a (E.UnboundVar (T.Ident b) _) = a == b
    
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
          "Unbound var: priv"
          (T.Rnode [lident "priv" `T.Assign` T.Number 1] `rref` "priv")
          (isUnboundVar "priv")
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
    , TestLabel "private access of public variable" . TestCase $
        assertEval
          (T.Rnode
             [ lsref "a" `T.Assign` T.Number 1
             , lsref "b" `T.Assign` rident "a"
             ]
           `rref` "b")
          (Number 1)
    , TestLabel "private access in nested scope of public variable" . TestCase $
        assertEval
          (T.Rnode
             [ lsref "a" `T.Assign` T.Number 1
             , lident "object"
               `T.Assign`
                 T.Rnode [ lsref "b" `T.Assign` rident "a" ]
             , lsref "c" `T.Assign` (rident "object" `rref` "b")
             ]
           `rref` "c")
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
    , TestLabel "unbound variable" . TestCase $
        assertError
          "Unbound var: c"
          (T.Rnode 
             [ lsref "a" `T.Assign` T.Number 2
             , lsref "b" `T.Assign` (rident "c" `_add_` T.Number 1)
             ]
           `rref` "b")
          (isUnboundVar "c")
    , TestLabel "undefined variable" . TestCase $
        let
          node = 
            T.Rnode
              [ T.Declare (lsref' "a")
              , lsref "b" `T.Assign` T.Number 1
              ]
        in
          do{ assertEval (node `rref` "b") (Number 1)
            ; assertError "Unbound var '.a'" (node `rref` "a") (isUnboundVar "a")
            }
    , TestLabel "unset variable forwards" . TestCase $
        assertError
          "Unbound var: c"
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
          (isUnboundVar "c")
    , TestLabel "unset variable backwards" . TestCase $
        assertError
          "Unbound var: c"
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
          (isUnboundVar "c")
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
    , TestLabel "unpack visible privately" . TestCase $
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
      , TestLabel "local private variable unpack visible publicly  ##depreciated behaviour" . TestCase $
          assertEval 
            (T.Rnode
               [ lident "w1" `T.Assign` T.Rnode [lsref "a" `T.Assign` T.Number 1]
               , T.Unpack (rident "w1")
               , lsref "b" `T.Assign` rident "a"
               ]
             `rref` "a")
            (Number 1)
      , TestLabel "local private variable unpack visible privately ##depreciated behaviour" . TestCase $
         assertEval
            (T.Rnode
               [ lident "w1" `T.Assign` T.Rnode [lsref "a" `T.Assign` T.Number 1]
               , T.Unpack (rident "w1")
               , lsref "b" `T.Assign` rident "a"
               ]
             `rref` "b")
            (Number 1)
      , TestLabel "local public variable unpack visible publicly ##depreciated behaviour" . TestCase $
          assertEval 
            (T.Rnode
               [ lsref "w1" `T.Assign` T.Rnode [lsref "a" `T.Assign` T.Number 1]
               , T.Unpack (rsref "w1")
               , lsref "b" `T.Assign` rident "a"
               ]
             `rref` "a")
            (Number 1)
      , TestLabel "access member of object with local public variable unpack ##depreciated behaviour" . TestCase $
          assertEval 
            (T.Rnode
               [ lsref "w1" `T.Assign` T.Rnode [lsref "a" `T.Assign` T.Number 1]
               , T.Unpack (rsref "w1")
               , lsref "b" `T.Assign` T.Number 2
               ]
             `rref` "b")
            (Number 2)
      , TestLabel "local public variable unpack visible privately ##depreciated behaviour" . TestCase $
         assertEval
            (T.Rnode
               [ lsref "w1" `T.Assign` T.Rnode [lsref "a" `T.Assign` T.Number 1]
               , T.Unpack (rsref "w1")
               , lsref "b" `T.Assign` rident "a"
               ]
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
                   [ lident "var" `T.Assign` T.Number 1
                   , lsref "innerVar" `T.Assign` rident "var"
                   ]
             , lident "outer"
               `T.Assign`
                 T.Rnode
                   [ lident "var" `T.Assign` T.Number 2
                   , T.Unpack (rident "inner")
                   ]
             , lsref "a" `T.Assign` (rident "outer" `rref` "innerVar")
             ]
           `rref` "a")
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
    , TestLabel "application to referenced outer scope" . TestCase $
        assertEval
          (T.Rnode
             [ lident "y"
               `T.Assign`
                 T.Rnode 
                   [ lsref "a" `T.Assign` T.Number 1
                   , lident "b" `T.Assign` T.Number 2
                   , lsref "x"
                     `T.Assign`
                       T.Rnode
                         [ lsref "a" `T.Assign` rident "b" ]
                   ]
             , lsref "a"
               `T.Assign`
                 ((rident "y" `T.App` (rident "y" `rref` "x")) `rref` "a")
             ]
           `rref` "a")
          (Number 2)
    , TestLabel "application to nested object" . TestCase $
        assertEval
          (T.Rnode
             [ lident "y"
               `T.Assign`
                 T.Rnode 
                   [ lsref "a" `T.Assign` T.Number 1
                   , lsref "x"
                     `T.Assign`
                       T.Rnode
                         [ lsref "a" `T.Assign` T.Number 2
                         , T.Declare (lsref' "x")
                         ]
                   ]
             , lsref "a"
               `T.Assign`
                 (((rident "y" `rref` "x") `T.App` rident "y") `rref` "a")
             ]
           `rref` "a")
          (Number 1)
      , TestLabel "eval statement" . TestCase $
          assertEval
            (T.Rnode
               [ lident "a" `T.Assign` T.Number 1
               , T.Eval (rident "a")
               , lsref "b" `T.Assign` rident "a"
               ]
             `rref` "b")
            (Number 1)
      , TestLabel "eval unbound variable" . TestCase $
          assertError
            "Unbound var: x" 
            (T.Rnode
               [ lident "a" `T.Assign` T.Number 1
               , T.Eval (rident "x")
               , lsref "b" `T.Assign` rident "a"
               ]
             `rref` "b")
            (isUnboundVar "x")
    ]