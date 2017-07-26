{-# LANGUAGE FlexibleContexts #-}

module Test.Eval
  ( assertEval
  , tests
  )
  where

import Eval
  ( evalRval
  , runEval
  )
import Types.Eval
import qualified Types.Parser as T
import Types.Parser.Short
import qualified Types.Error as E

import Control.Monad.IO.Class( liftIO )
import Control.Monad.Reader( runReaderT )
import Control.Exception
import Test.HUnit
  ( Test(..)
  , Assertion
  , assertEqual
  , assertFailure
  , assertBool
  )
  
assertEval :: Rhs T.Rval a => a -> Value -> Assertion
assertEval a expected =
  do
    primEnv <- primitiveBindings
    v <- runEval (evalRval r) (primEnv, emptyEnv)
    assertEqual banner expected v
  where
    r = toRhs a
    banner = "Evaluatiing \"" ++ show r ++ "\""

    
assertError :: (Rhs T.Rval a, Exception e) => String -> a -> (e -> Bool) -> Assertion
assertError msg a test =
  catch
    (do
       primEnv <- primitiveBindings
       v <- runEval (evalRval r) (primEnv, emptyEnv)
       assertFailure (banner ++ expectedmsg msg v))
    (\ e -> if test e then return () else assertFailure (banner ++ expectedmsg msg e))
  where
    r = toRhs a
    banner = "Evaluating \"" ++ show r ++ "\""
    expectedmsg msg e = "\nexpected: " ++ msg ++ "\n but got: " ++ show e

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
          (node [lsref "pub" =: T.Number 1] `rref` "pub")
          (Number 1)
    , TestLabel "private variable" . TestCase $ 
        assertError
          "Unbound var: priv"
          (node [lident "priv" =: T.Number 1] `rref` "priv")
          (isUnboundVar "priv")
    , TestLabel "private variable access backward" . TestCase $
        assertEval
          (node
             [ lident "priv" =: T.Number 1
             , lsref "pub" =: rident "priv"
             ]
           `rref` "pub")
          (Number 1)
    , TestLabel "private variable access forward" . TestCase $
        assertEval
          (node
             [ lsref "pub" =: rident "priv"
             , lident "priv" =: T.Number 1
             ]
           `rref` "pub")
          (Number 1)
    , TestLabel "private access of public variable" . TestCase $
        assertEval
          (node
             [ lsref "a" =: T.Number 1
             , lsref "b" =: rident "a"
             ]
           `rref` "b")
          (Number 1)
    , TestLabel "private access in nested scope of public variable" . TestCase $
        assertEval
          (node
             [ lsref "a" =: T.Number 1
             , lident "object"
               =:
                 node [ lsref "b" =: rident "a" ]
             , lsref "c" =: (rident "object" `rref` "b")
             ]
           `rref` "c")
          (Number 1)
    , TestLabel "access backward public variable from same scope" . TestCase $
        assertEval
          (node
             [ lsref "b" =: T.Number 2
             , lsref "a" =: rsref "b" 
             ]
           `rref` "a")
          (Number 2)
    , TestLabel "access forward public variable from same scope" . TestCase $
        assertEval
          (node
             [ lsref "a" =: rsref "b"
             , lsref "b" =: T.Number 2
             ]
           `rref` "a")
          (Number 2)
    , TestLabel "unbound variable" . TestCase $
        assertError
          "Unbound var: c"
          (node 
             [ lsref "a" =: T.Number 2
             , lsref "b" =: (rident "c" `_add_` T.Number 1)
             ]
           `rref` "b")
          (isUnboundVar "c")
    , TestLabel "undefined variable" . TestCase $
        let
          v =
            node
              [ var (lsref' "a")
              , lsref "b" =: T.Number 1
              ]
        in
          do
            assertEval (v `rref` "b") (Number 1)
            assertError "Unbound var '.a'" (v `rref` "a") (isUnboundVar "a")
    , TestLabel "unset variable forwards" . TestCase $
        assertError
          "Unbound var: c"
          (node
             [ lident "c" =: T.Number 1
             , lident "b"
               =:
                 node
                   [ var (lident' "c")
                   , lsref "a" =: rident "c"
                   ]
             , lsref "ba" =: (rident "b" `rref` "a")
             ]
           `rref` "ba")
          (isUnboundVar "c")
    , TestLabel "unset variable backwards" . TestCase $
        assertError
          "Unbound var: c"
          (node
             [ lident "c" =: T.Number 1
             , lident "b"
               =:
                 node
                   [ lsref "a" =: rident "c"
                   , var "c"
                   ]
             , lsref "ba" =: (rident "b" `rref` "a")
             ]
           `rref` "ba")
          (isUnboundVar "c")
    , TestLabel "application  overriding public variable" . TestCase $
        assertEval
          ((node 
              [ lsref "a" =: T.Number 2
              , lsref "b" =: (rsref "a" `_add_` T.Number 1)
              ]
            `T.App` node [lsref "a" =: T.Number 1])
           `rref` "b")
          (Number 2)
    , TestLabel "default definition forward" . TestCase $
        assertEval
          ((node
              [ lsref "a" =: (rsref "b" `_sub_` T.Number 1)
              , lsref "b" =: (rsref "a" `_add_` T.Number 1)
              ]
            `T.App` node [ lsref "b" =: T.Number 2])
            `rref` "a")
          (Number 1)
    , TestLabel "default definition backward" . TestCase $
        assertEval
          ((node
              [ lsref "a" =: (rsref "b" `_sub_` T.Number 1)
              , lsref "b" =: (rsref "a" `_add_` T.Number 1)
              ]
            `T.App` node [ lsref "a" =: T.Number 2])
            `rref` "b")
          (Number 3)
    , TestLabel "route getter" . TestCase $
        assertEval
          ((node
              [ lsref "a" 
                =:
                  node [ lsref "aa" =: T.Number 2 ]
              ]
            `rref` "a")
            `rref` "aa")
          (Number 2)
    , TestLabel "route setter" . TestCase $
        assertEval
          ((node
              [ (lsref' "a" `lref` "aa")
              =: T.Number 2
              ]
            `rref` "a")
            `rref` "aa")
          (Number 2)
    , TestLabel "application overriding nested property" . TestCase $
        assertEval
          ((node
              [ lsref "a" =: node [lsref "aa" =: T.Number 0]
              , lsref "b" =: (rsref "a" `rref` "aa")
              ]
            `T.App`
              node [(lsref' "a" `lref` "aa") =: T.Number 1])
            `rref` "b")
          (Number 1)
    , TestLabel "shadowing update" . TestCase $
        assertEval
          ((node
              [ lident "outer" =: node [lsref "a" =: T.Number 1]
              , lsref "inner"
                =:
                  node
                    [ (lident' "outer" `lref` "b") =: T.Number 2
                    , lsref "ab"
                      =: 
                        ((rident "outer" `rref` "a") `_add_` (rident "outer" `rref` "b"))
                    ]
              ]
            `rref` "inner")
            `rref` "ab")
          (Number 3)
    , TestLabel "shadowing update 2" . TestCase $
        assertEval
          (node
             [ lident "outer"
               =:
                 node
                   [ lsref "a" =: T.Number 2
                   , lsref "b" =: T.Number 1
                   ]
             , lsref "inner"
               =: node [(lsref' "outer" `lref` "b") =: T.Number 2]
             , lsref "ab"
               =:
                 ((rident "outer" `rref` "a") `_add_` (rident "outer" `rref` "b"))
             ]
           `rref` "ab")
          (Number 3)
    , TestLabel "destructuring" . TestCase $
        let
          v = 
            node
              [ lident "obj"
                =:
                  node
                    [ lsref "a" =: T.Number 2
                    , lsref "b" =: T.Number 3
                    ]
              , lnode
                  [ plainsref "a" =: lsref "da"
                  , plainsref "b" =: lsref "db"
                  ]
                =: rident "obj"
              ]
        in
          do{ assertEval (v `rref` "da") (Number 2)
            ; assertEval (v `rref` "db") (Number 3)
            }
    , TestLabel "destructuring unpack" . TestCase $
        assertEval
          ((node
              [ lident "obj"
                =:
                  node
                    [ lsref "a" =: T.Number 2
                    , lsref "b" =: T.Number 3
                    ]
              , lnode
                  [ plainsref "a" =: lsref "da"
                  , error "unpack" -- T.ReversibleUnpack (lsref "dobj")
                  ]
                =: rident "obj"
              ]
            `rref` "dobj")
            `rref` "b")
          (Number 3)
    , TestLabel "nested destructuring" . TestCase $
        let 
          rnode =
            node
              [ lident "y1"
                =:
                  node
                    [ lsref "a"
                      =:
                        node
                          [ lsref "aa" =: T.Number 3
                          , lsref "ab" =: node [lsref "aba" =: T.Number 4]
                          ]
                    ]
              , lnode
                  [ (plainsref "a" `plainref` "aa") =: lsref "da"
                  , ((plainsref "a" `plainref` "ab") `plainref` "aba") =: lsref "daba"
                  ]
                =: rident "y1"
              , lsref "raba"
                  =:
                    ("y1" .: "a" .: "ab" .: "aba")
              ]
        in
          do{ assertEval (rnode `rref` "raba") (Number 4)
            ; assertEval (rnode `rref` "daba") (Number 4)
            }
    , TestLabel "unpack visible publicly" . TestCase $
        let
          rnode =
            node
              [ lident "w1" =: node [lsref "a" =: T.Number 1]
              , lsref "w2"
                =:
                  node
                    [ lsref "b" =: rsref "a"
                    , error "unpack" -- T.Unpack (rident "w1")
                    ]
              , lsref "w3" =: dot "w2" .:  "a"
              ]
        in
          do{ assertEval ((rnode `rref` "w2") `rref` "b") (Number 1)
            ; assertEval (rnode `rref` "w3") (Number 1)
            }
    , TestLabel "unpack visible privately" . TestCase $
        assertEval
          ((node
              [ lident "w1" =: node [lsref "a" =: T.Number 1]
              , lsref "w2"
                =:
                  node
                    [ lsref "b" =: rident "a"
                    , error "unpack" -- T.Unpack $ rident "w1"
                    ]
              ]
            `rref` "w2")
            `rref` "b")
          (Number 1)
      , TestLabel "local private variable unpack visible publicly  ##depreciated behaviour" . TestCase $
          assertEval 
            (node
               [ lident "w1" =: node [lsref "a" =: T.Number 1]
               , error "unpack" -- T.Unpack (rident "w1")
               , lsref "b" =: rident "a"
               ]
             `rref` "a")
            (Number 1)
      , TestLabel "local private variable unpack visible privately ##depreciated behaviour" . TestCase $
         assertEval
            (node
               [ lident "w1" =: node [lsref "a" =: T.Number 1]
               , error "unpack" -- T.Unpack (rident "w1")
               , lsref "b" =: rident "a"
               ]
             `rref` "b")
            (Number 1)
      , TestLabel "local public variable unpack visible publicly ##depreciated behaviour" . TestCase $
          assertEval 
            (node
               [ lsref "w1" =: node [lsref "a" =: T.Number 1]
               , error "unpack" -- T.Unpack (rsref "w1")
               , lsref "b" =: rident "a"
               ]
             `rref` "a")
            (Number 1)
      , TestLabel "access member of object with local public variable unpack ##depreciated behaviour" . TestCase $
          assertEval 
            (node
               [ lsref "w1" =: node [lsref "a" =: T.Number 1]
               , error "unpack" -- T.Unpack (rsref "w1")
               , lsref "b" =: T.Number 2
               ]
             `rref` "b")
            (Number 2)
      , TestLabel "local public variable unpack visible privately ##depreciated behaviour" . TestCase $
         assertEval
            (node
               [ lsref "w1" =: node [lsref "a" =: T.Number 1]
               , error "unpack" -- T.Unpack (rsref "w1")
               , lsref "b" =: rident "a"
               ]
             `rref` "b")
            (Number 1)
    , TestLabel "parent scope binding" . TestCase $
        assertEval
          ((node
              [ lsref "inner" =: T.Number 1
              , lident "parInner" =: rsref "inner"
              , lsref "outer"
                =:
                  node
                    [ lsref "inner" =: T.Number 2
                    , lsref "a" =: rident "parInner"
                    ]
              ]
            `rref` "outer")
            `rref` "a")
          (Number 1)
    , TestLabel "unpack scope binding" . TestCase $
        assertEval
          (node
             [ lident "inner"
               =:
                 node
                   [ lident "var" =: T.Number 1
                   , lsref "innerVar" =: rident "var"
                   ]
             , lident "outer"
               =:
                 node
                   [ lident "var" =: T.Number 2
                   , error $ "unpack" -- T.Unpack (rident "inner")
                   ]
             , lsref "a" =: (rident "outer" `rref` "innerVar")
             ]
           `rref` "a")
          (Number 1)
    , TestLabel "self referencing definition" . TestCase $
        assertEval
          (node
             [ lident "y"
               =:
                 node
                   [ lsref "a" =: (rident "y" `rref` "b")
                   , lsref "b" =: T.Number 1
                   ]
             , lsref "z" =: (rident "y" `rref` "a")
             ]
           `rref` "z")
          (Number 1)
    , TestLabel "application to referenced outer scope" . TestCase $
        assertEval
          (node
             [ lident "y"
               =:
                 node 
                   [ lsref "a" =: T.Number 1
                   , lident "b" =: T.Number 2
                   , lsref "x"
                     =:
                       node
                         [ lsref "a" =: rident "b" ]
                   ]
             , lsref "a"
               =:
                 ((rident "y" $: (rident "y" `rref` "x")) `rref` "a")
             ]
           `rref` "a")
          (Number 2)
    , TestLabel "application to nested object" . TestCase $
        assertEval
          (node
             [ "y" =:
                 node
                   [ "a" =: T.Number 1
                   , dot "x" =:
                       node
                         [ dot "a" =: T.Number 2
                         , var (dot "x")
                         ]
                   ]
             , dot "a" =: "y" .: "x" $: ("y" .: "a")
             ]
           .: "a")
          (Number 1)
      , TestLabel "eval statement" . TestCase $
          assertEval
            (node
               [ "a" =: T.Number 1
               , eval "a"
               , dot "b" =: "a"
               ]
             .: "b")
            (Number 1)
      , TestLabel "eval unbound variable" . TestCase $
          assertError
            "Unbound var: x" 
            (node
               [ "a" =: T.Number 1
               , eval "x"
               , dot "b" =: "a"
               ]
             .: "b")
            (isUnboundVar "x")
    ]