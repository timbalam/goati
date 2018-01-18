{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Types.Primop
  where

import Data.Functor.Classes
import System.IO( Handle )

-- Primitive my-language expression
data P a = 
    NAdd Double a
  | NSub Double a
  | NProd Double a
  | NDiv Double a
  | NPow Double a
  | NEq Double a
  | NNe Double a
  | NLt Double a
  | NGt Double a
  | NLe Double a
  | NGe Double a
  | HGetLine Handle a a
  | HGetContents Handle a a
  | HPutStr Handle a a a
  | HPutChar Handle a a a
  deriving (Show, Eq, Functor, Foldable, Traversable)

  
instance Eq1 P where
  liftEq eq (NAdd da a) (NAdd db b) = da == db && eq a b
  liftEq eq (NSub da a) (NSub db b) = da == db && eq a b
  liftEq eq (NProd da a) (NProd db b) = da == db && eq a b
  liftEq eq (NDiv da a) (NDiv db b) = da == db && eq a b
  liftEq eq (NPow da a) (NPow db b) = da == db && eq a b
  liftEq eq (NEq da a) (NEq db b) = da == db && eq a b
  liftEq eq (NNe da a) (NNe db b) = da == db && eq a b
  liftEq eq (NLt da a) (NLt db b) = da == db && eq a b
  liftEq eq (NGt da a) (NGt db b) = da == db && eq a b
  liftEq eq (NLe da a) (NLe db b) = da == db && eq a b
  liftEq eq (NGe da a) (NGe db b) = da == db && eq a b
  liftEq eq (HGetLine ha era sua) (HGetLine hb erb sub) =
    ha == hb && eq era erb && eq sua sub
  liftEq eq (HGetContents ha era sua) (HGetContents hb erb sub) =
    ha == hb && eq era erb && eq sua sub
  liftEq eq (HPutStr ha a era sua) (HPutStr hb b erb sub) =
    ha == hb && eq a b && eq era erb && eq sua sub
  liftEq eq (HPutChar ha a era sua) (HPutChar hb b erb sub) =
    ha == hb && eq a b && eq era erb && eq sua sub
  liftEq _ _ _ = False
  
  
instance Show1 P where
  liftShowsPrec f g i e = case e of
    NAdd d a -> shownum "NAdd" i d a
    NSub d a -> shownum "NSub" i d a
    NProd d a -> shownum "NProd" i d a
    NDiv d a -> shownum "NDiv" i d a
    NPow d a -> shownum "NPow" i  d a
    NEq d a -> shownum "NEq" i d a
    NNe d a -> shownum "NNe" i d a
    NLt d a -> shownum "NLt" i d a
    NGt d a -> shownum "NGt" i d a
    NLe d a -> shownum "NLe" i d a
    NGe d a -> shownum "NGe" i d a
    HGetContents h er su -> showhget "HGetContents" i h er su
    HGetLine h er su -> showhget "HGetLine" i h er su
    HPutStr h a er su -> showhput "HPutStr" i h a er su
    HPutChar h a er su -> showhput "HPutChar" i h a er su
    where
      shownum = showsBinaryWith showsPrec f
      showhget name i h er su = showParen (i > 10)
        (showString name . showChar ' ' . showsPrec 11 h
          . showChar ' ' . f 11 er  . showChar ' ' . f 11 su)
      showhput name i h a er su = showParen (i > 10)
        (showString name . showChar ' ' . showsPrec 11 h
          . showChar ' ' . f 11 a . showChar ' ' . f 11 er
          . showChar ' ' . f 11 su)

      
