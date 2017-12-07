{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module Test.Parser.Short
  ( tests
  )
  where

import Types.Parser.Short
import Types.Classes

import Data.Function( (&) )
import Data.Foldable( traverse_ )
import Control.Monad.Free
import Test.HUnit
  ( Test(..)
  , Assertion
  , assertEqual
  , assertFailure
  , assertBool
  )
  
  
banner :: ShowMy a => a -> String
banner a = "For " ++ showMy a ++ ","
  
  
type E = Expr (Vis Tag)


tests =
  TestList
    [ TestLabel "integer literal" . TestCase $ let
        r = 20 :: E
        e = IntegerLit 20
        in
          assertEqual (banner r) e r
          
    , TestLabel "addition" . TestCase $ let
        r = 1 #+ 1 :: E
        e = IntegerLit 1 & Binop Add $ IntegerLit 1
        in
          assertEqual (banner r) e r
          
    , TestLabel "floating literal" . TestCase $ let
        r = 0.5 :: E
        e = NumberLit 0.5
        in
          assertEqual (banner r) e r
          
    , TestLabel "subtraction" . TestCase $ let
        r = 1.0 #- 2.0 :: E
        e = NumberLit 1 & Binop Sub $ NumberLit 2
        in
          assertEqual (banner r) e r
    
    , TestLabel "ops" . TestCase $
        let
          ops =
            [ (Binop Add, (#+))
            , (Binop Sub, (#-))
            , (Binop Prod, (#*))
            , (Binop Div, (#/))
            , (Binop Pow, (#^))
            ]
          testop (o, f) = let
            e = IntegerLit 1 `o` IntegerLit 2
            r = 1 `f` 2
            in
              assertEqual (banner r) e r
        in
          traverse_ testop ops
          
    , TestLabel "comparisons" . TestCase $
        let
          cmps = 
            [ (Binop Lt, (#<))
            , (Binop Le, (#<=))
            , (Binop Gt, (#>))
            , (Binop Ge, (#>=))
            , (Binop Eq, (#==))
            , (Binop Ne, (#!=))
            ]
          testcmp (o,  f) = let
            e = NumberLit 2 `o` NumberLit 0.2
            r = 2.0 `f` 0.2
            in
              assertEqual (banner r) e r
        in
          traverse_ testcmp cmps
          
    , TestLabel "string literal" . TestCase $ let
        r = "hello" :: E
        e = StringLit "hello"
        in
          assertEqual (banner r) e r
          
    , TestLabel "variable" . TestCase $ let
        r = self' "pub" :: E
        e = Var (Pub "pub")
        in
          assertEqual (banner r) e r
        
    , TestLabel "path" . TestCase $ let
        r = self' "pub" #. "x" #. "y" :: E
        e = (Get (Get (Var (Pub "pub") `At` "x") `At` "y"))
        in
          assertEqual (banner r) e r
          
    , TestLabel "negation" . TestCase $ let
        r = -(env' "hi") :: E
        e = (Unop Neg . Var) (Priv "hi")
        in
          assertEqual (banner r) e r
          
    , TestLabel "not" . TestCase $ let
        r = not' (env' "true") :: E
        e = (Unop Not . Var) (Priv "true")
        in
          assertEqual (banner r) e r
        
    , TestLabel "update" . TestCase $ let
        r = env' "a" # env' "b" :: E
        e = Var (Priv "a") `Update` Var (Priv "b")
        in
          assertEqual (banner r) e r
        
    , TestLabel "update path" . TestCase $ let
        r = env' "a" #. "x" # env' "b" #. "y" :: E
        e = Get ((Get (Var (Priv "a") `At` "x") `Update` Var (Priv "b")) `At` "y")
        in
          assertEqual (banner r) e r
        
    , TestLabel "block" . TestCase $ let
        r = block' [ env' "a" #= env' "b" ] :: E
        e = block' [SetPath (Pure (Priv "a")) `Set` Var (Priv "b")]
        in
          assertEqual (banner r) e r
        
    , TestLabel "set path" . TestCase $ let
        r = block' [ env' "a" #. "x" #= 1 ] :: E
        e = block' [SetPath (Free (Pure (Priv "a") `At` "x")) `Set` IntegerLit 1]
        in
          assertEqual (banner r) e r
        
    , TestLabel "set pun" . TestCase $ let
        r = block' [ self' "pun" ] :: E
        e = block' [SetPun (Pure (Pub "pun"))]
        in
          assertEqual (banner r) e r
        
    , TestLabel "set pun path" . TestCase $ let
        r = block' [ self' "pun" #. "path" ] :: E
        e = block' [SetPun (Free (Pure (Pub "pun") `At` "path"))]
        in
          assertEqual (banner r) e r
        
    , TestLabel "block with multiple statements" . TestCase $ let
        r = block' [
          env' "var" #= 1,
          env' "path" #. "f" #=
            env' "var" #+ 1,
          self' "field" 
          ] :: E
        e = block' [
          SetPath (Pure (Priv "var")) `Set` IntegerLit 1,
          SetPath (Free (Pure (Priv "path") `At` "f")) `Set`
            (Var (Priv "var") & Binop Add $ IntegerLit 1),
          SetPun (Pure (Pub "field"))
          ]
        in
          assertEqual (banner r) e r
        
    , TestLabel "destructure" . TestCase $ let
        r = block' [
          setblock' [ self' "x" #= self' "y" ] #=
            env' "val"
          ] :: E
        e = block' [
          setblock' [Pure "x" `Match` SetPath (Pure (Pub "y"))] `Set`
            Var (Priv "val")
          ]
        in
        assertEqual (banner r) e r
        
    , TestLabel "destructure path" . TestCase $ let
        r = block' [
          setblock' [
            self' "x" #. "f" #=
              env' "y" #. "f"
            ] #= env' "val"
          ] :: E
        e = block' [
          setblock' [
            Free (Pure "x" `At` "f") `Match`
              SetPath (Free (Pure (Priv "y") `At` "f"))
            ] `Set` Var (Priv "val")
          ]
        in
          assertEqual (banner r) e r
        
    , TestLabel "destructure pun" . TestCase $ let
        r = block' [
          setblock' [ env' "y" #. "f" ] #=
            env' "val"
          ] :: E
        e = block' [
          setblock' [MatchPun (Free (Pure (Priv "y") `At` "f"))] `Set`
            Var (Priv "val")
          ]
        in
          assertEqual (banner r) e r
          
    , TestLabel "destructure with multiple statements" . TestCase $ let
        r = block' [
          setblock' [
            env' "y" #. "f",
            self' "y" #. "g" #= env' "g"
            ] #= env' "x"
          ] :: E
        e = block' [
          setblock' [
            MatchPun (Free (Pure (Priv "y") `At` "f")),
            Free (Pure "y" `At` "g") `Match` SetPath (Pure (Priv "g"))
            ] `Set` Var (Priv "x")
          ]
        in
          assertEqual (banner r) e r
          
    , TestLabel "nested destructure" . TestCase $ let
        r = block' [
          setblock' [ self' "x" #=
            setblock' [ self' "f" #= env' "f" ]
            ] #=
            block' [
              self' "x" #. "f" #=
                1
              ]
          ] :: E
        e = block' [
          setblock' [ Pure "x" `Match`
            setblock' [ Pure "f" `Match` SetPath (Pure (Priv "f")) ]
            ] `Set`
            block' [
              SetPath (Free (Pure (Pub "x") `At` "f")) `Set`
                IntegerLit 1
              ]
          ]
        in
          assertEqual (banner r) e r
    
    , TestLabel "block with destructure and other statements" . TestCase $ let
        r = block' [
          self' "x" #. "f" #= "abc",
          setblock' [ env' "a" ] #= env' "var" #. "f"
          ] :: E
        e = block' [
          SetPath (Free (Pure (Pub "x") `At` "f")) `Set` StringLit "abc",
          setblock' [MatchPun (Pure (Priv "a"))] `Set` Get (Var (Priv "var") `At` "f")
          ]
        in 
          assertEqual (banner r) e r
    ]