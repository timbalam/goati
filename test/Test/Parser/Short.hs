{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module Test.Parser.Short
  ( tests
  )
  where

import Types.Parser.Short
import Types.Parser
import Parser( Vis(..) )

import Data.Function( (&) )
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


instance ShowMy a => Show (Expr a) where
  show = showMy


tests =
  TestList
    [ TestLabel "integer literal" . TestCase $ let r = parse 20 in
        assertEqual (banner r) (IntegerLit 20) r
          
    , TestLabel "add" . TestCase $ let r = parse (1 .+ 1) in
        assertEqual (banner r) (IntegerLit 1 & Binop Add $ IntegerLit 1) r
          
    , TestLabel "floating literal" . TestCase $ let r = parse 0.5 in
        assertEqual (banner r) (NumberLit 0.5) r
          
    , TestLabel "subtract" . TestCase $ let r = parse (1.0 .- 2.0) in
        assertEqual (banner r) (NumberLit 1 & Binop Sub $ NumberLit 2) r
    
    , TestLabel "ops" . TestCase $
        let
          ops =
            [ (Binop Add, (.+))
            , (Binop Sub, (.-))
            , (Binop Prod, (.*))
            , (Binop Div, (./))
            , (Binop Pow, (.^))
            ]
        in
          sequence_
            (map (\ (o, f) -> let
              e = o (IntegerLit 1) (IntegerLit 2)
              r = parse (1 `f` 2) in
              assertEqual (banner r) e r) ops)
          
    , TestLabel "variable" . TestCase $ let r = parse (self "pub") in
        assertEqual (banner r) (Var (Pub "pub")) r
        
    , TestLabel "path" . TestCase $ let r = parse (self "pub" :. "x" :. "y") in
        assertEqual (banner r) (Get (Get (Var (Pub "pub") `At` "x") `At` "y")) r
        
    , TestLabel "update" . TestCase $ let r = parse (env "a" .$ env "b") in
        assertEqual (banner r) (Update (Var (Priv "a")) (Var (Priv "b"))) r
        
    , TestLabel "update path" . TestCase $ let r = parse (env "a" :. "x" .$ env "b" :. "y") in
        assertEqual (banner r) (Get (Update (Get (Var (Priv "a") `At` "x")) (Var (Priv "b")) `At` "y")) r
        
    , TestLabel "block" . TestCase $ let r = parse (b [ env "a" := env "b" ]) in
        assertEqual (banner r) (Block [SetPath (Pure (Priv "a")) `Set` Var (Priv "b")]) r
        
    , TestLabel "set path" . TestCase $ let r = parse (b [ env "a" :. "x" := 1 ]) in
        assertEqual (banner r) (Block [SetPath (Free (Pure (Priv "a") `At` "x")) `Set` IntegerLit 1]) r
    ]