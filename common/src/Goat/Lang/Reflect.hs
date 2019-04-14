{-# LANGUAGE RankNTypes #-}
module Goat.Lang.Reflect
  where

import Goat.Comp
import Goat.Prism
import Goat.Lang.Comment
import Goat.Lang.Number

infixr 1 <:

-- | Open union
data (f <: g) a = Head (f a) | Tail (g a)
data Null a

_Head :: Prism ((h <: t) a) ((h' <: t) a) (h a) (h' a)
_Head = prism Head (either Right (Left . Tail) . decomp)

_Tail :: Prism ((h <: t) a) ((h <: t') a) (t a) (t' a)
_Tail = prism Tail (either (Left . Head) Right . decomp)

handle
 :: (forall x . h x -> (x -> Comp t a) -> Comp t a)
 -> Comp (h <: t) a -> Comp t a
handle f =
  iter (\ r k -> either f Req (decomp r) k) Done

handleWith
 :: Traversable h => (h a -> a) -> Comp (h <: t) a -> Comp t a
handleWith f = handle (\ a k -> f <$> traverse k a)

handleAll
 :: (Comp r a -> Comp Null a) -> Comp r Void -> a
handleAll f = run . f . vacuous

run :: Comp Null a -> a
run = iter (\ a _ -> absurdU a) id

-- | Comment
instance Member Comment (Comment <: t) where uprism = _Head
instance Member Number t => Member Number (Comment <: t) where
  uprism = _Tail . uprism
  
showCommentR :: Comp (Comment <: t) ShowS -> Comp t ShowS
showCommentR = handleWith (showComment id)

fromCommentR
 :: Comment_ r => Comment (Comment <: t) r -> Comment t r
fromCommentR = handleWith (fromComment id)

-- | Number
instance Member Number (Number <: t) where uprism = _Head
instance Member Comment t => Member Comment (Number <: t) where
  uprism = _Tail . uprism

showNumberR :: Comp (Number <: t) ShowS -> Comp t ShowS
showNumberR = handleWith showNumber

fromNumberR :: Fractional r => Comp (Number <: t) r -> Comp t r
fromNumberR = handleWith fromNumber


