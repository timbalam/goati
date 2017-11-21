{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module Test.Parser.Short
  ( tests
  )
  where

import Types.Parser.Short
import Types.Parser
import Parser( Vis(..) )

import Data.Function( (&) )
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
    [ TestLabel "integer literal" . TestCase $ let r = 20 :: Expr (Vis Tag) in
        assertEqual (banner r) (IntegerLit 20) r
          
    , TestLabel "add" . TestCase $ let r = 1 + 1 :: Expr (Vis Tag) in
        assertEqual (banner r) (IntegerLit 1 & Binop Add $ IntegerLit 1) r
          
    , TestLabel "subtract" . TestCase $ let r = 1.0 - 2.0 :: Expr (Vis Tag) in
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
              
          i = iterate (+1) 1
          j = iterate (+2) 1
        in
          sequence_
            (zipWith
              (\ r e -> assertEqual (banner r) e r)
              (zipWith3 fst ops i j)
              (zipWith3 snd ops i j))
          
    , TestLabel "floating literal" . TestCase $ let r = 0.5 :: Expr (Vis Tag) in
        assertEqual (banner r) (NumberLit 0.5) r
          
    , TestLabel "variable" . TestCase $
        assertEqual "" (Var (Pub "pub")) (toExpr (Pub "pub" :: Vis Tag))
    ]