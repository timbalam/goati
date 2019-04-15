{-# LANGUAGE RankNTypes, TypeOperators, EmptyCase, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, TypeFamilies #-}
module Goat.Lang.Reflect
  ( module Goat.Comp
  , (<:)(), Null, decomp, _Head, _Tail, handle, handleAll, run, raise
  , showCommentM, fromCommentM
  , showNumberM, fromNumberM
  , showArithBMPrec, fromArithBM
  , showCmpBMPrec, fromCmpBM
  , showLogicBMPrec, fromLogicBM
  , showUnopMPrec, fromUnopM
  , showBlockM, fromBlockM
  , showTextM, fromTextM
  , showVarM, fromVarM
  , showChainM, fromChainM
  , showExternM, fromExternM
  , showExtendM, fromExtendM
  )
  where

import Goat.Comp
import Goat.Prism
import Goat.Lang.Comment
import Goat.Lang.Number
import Goat.Lang.ArithB
import Goat.Lang.CmpB
import Goat.Lang.LogicB
import Goat.Lang.Unop
import Goat.Lang.Block
import Goat.Lang.Text
import Goat.Lang.Ident
import Goat.Lang.Field
import Goat.Lang.Extern
import Goat.Lang.Extend
import Data.Void

infixr 1 <:

-- | Open union
data (f <: g) a = Head (f a) | Tail (g a)
data Null a

decomp :: (h <: t) a -> Either (h a) (t a)
decomp (Head h) = Left h
decomp (Tail t) = Right t

_Head :: Prism ((h <: t) a) ((h' <: t) a) (h a) (h' a)
_Head = prism Head (either Right (Left . Tail) . decomp)

_Tail :: Prism ((h <: t) a) ((h <: t') a) (t a) (t' a)
_Tail = prism Tail (either (Left . Head) Right . decomp)

raise :: Comp t a -> Comp (h <: t) a
raise = hoist Tail

handle
 :: (forall x . h x -> (x -> Comp t a) -> Comp t a)
 -> Comp (h <: t) a -> Comp t a
handle f =
  iter (\ r k -> either f Req (decomp r) k) Done

handleAll
 :: (Comp r a -> Comp Null a) -> Comp r Void -> a
handleAll f = run . f . vacuous

run :: Comp Null a -> a
run = iter (\ a _ -> case a of {}) id

-- | Comment
instance Member Comment (Comment <: t) where uprism = _Head
  
showCommentM :: Comp (Comment <: t) ShowS -> Comp t ShowS
showCommentM = handle showComment

fromCommentM
 :: Comment_ r => Comp (Comment <: t) r -> Comp t r
fromCommentM = handle fromComment

-- | Number
instance Member Number (Number <: t) where uprism = _Head

instance Member Comment t => Member Comment (Number <: t) where
  uprism = _Tail . uprism
instance Member Number t => Member Number (Comment <: t) where
  uprism = _Tail . uprism

showNumberM :: Comp (Number <: t) ShowS -> Comp t ShowS
showNumberM = handle (const . pure . showNumber)

fromNumberM :: Fractional r => Comp (Number <: t) r -> Comp t r
fromNumberM = handle (const . pure . fromNumber)

-- | ArithB
instance Member ArithB (ArithB <: t) where uprism = _Head

instance Member Comment t => Member Comment (ArithB <: t) where
  uprism = _Tail . uprism
instance Member ArithB t => Member ArithB (Comment <: t) where
  uprism = _Tail . uprism

instance Member Number t => Member Number (ArithB <: t) where
  uprism = _Tail . uprism
instance Member ArithB t => Member ArithB (Number <: t) where
  uprism = _Tail . uprism

showArithBMPrec
 :: Applicative m
 => (Comp (ArithB <: t) ShowS -> m ShowS)
 -> Comp (ArithB <: t) ShowS -> m ShowS
showArithBMPrec = 
  showAddMPrec . showMulMPrec . showPowMPrec
  where
    showAddMPrec, showMulMPrec, showPowMPrec
     :: Applicative m
     => (Comp (ArithB <: t) ShowS -> m ShowS)
     -> Comp (ArithB <: t) ShowS -> m ShowS
    showAddMPrec sp (Req (Head (a :#+ b)) k) =
      showArithB (sp (k a) :#+ showAddMPrec sp (k b)) id
    showAddMPrec sp (Req (Head (a :#- b)) k) =
      showArithB (sp (k a) :#- showAddMPrec sp (k b)) id
    showAddMPrec sp m = sp m

    showMulMPrec sp (Req (Head (a :#* b)) k) =
      showArithB (sp (k a) :#* showMulMPrec sp (k b)) id
    showMulMPrec sp (Req (Head (a :#/ b)) k) =
      showArithB (sp (k a) :#/ showMulMPrec sp (k b)) id
    showMulMPrec sp m = sp m
    
    showPowMPrec sp (Req (Head (a :#^ b)) k) =
      showArithB (showPowMPrec sp (k a) :#^ sp (k b)) id
    showPowMPrec sp m = sp m

fromArithBM :: ArithB_ r => Comp (ArithB <: t) r -> Comp t r
fromArithBM = handle fromArithB

-- | CmpB
instance Member CmpB (CmpB <: t) where uprism = _Head

instance Member Comment t => Member Comment (CmpB <: t) where
  uprism = _Tail . uprism
instance Member CmpB t => Member CmpB (Comment <: t) where
  uprism = _Tail . uprism

instance Member Number t => Member Number (CmpB <: t) where
  uprism = _Tail . uprism
instance Member CmpB t => Member CmpB (Number <: t) where
  uprism = _Tail . uprism

instance Member ArithB t => Member ArithB (CmpB <: t) where
  uprism = _Tail . uprism
instance Member CmpB t => Member CmpB (ArithB <: t) where
  uprism = _Tail . uprism

showCmpBMPrec
 :: Applicative m
 => (Comp (CmpB <: t) ShowS -> m ShowS)
 -> Comp (CmpB <: t) ShowS -> m ShowS
showCmpBMPrec = showCmpBMPrec'
  where
    showCmpBMPrec' sp (Req (Head h) k) = case h of
      a :#== b -> hdl (:#==) a b
      a :#!= b -> hdl (:#!=) a b
      a :#>  b -> hdl (:#>) a b
      a :#>= b -> hdl (:#>=) a b
      a :#<  b -> hdl (:#<) a b
      a :#<= b -> hdl (:#<=) a b
      where
        hdl op a b = do
          showCmpB (sp (k a) `op` sp (k b)) id
    showCmpBMPrec' sp m = sp m

fromCmpBM
 :: CmpB_ r => Comp (CmpB <: t) r -> Comp t r
fromCmpBM = handle fromCmpB

-- | LogicB
instance Member LogicB (LogicB <: t) where uprism = _Head

instance Member Comment t => Member Comment (LogicB <: t) where
  uprism = _Tail . uprism
instance Member LogicB t => Member LogicB (Comment <: t) where
  uprism = _Tail . uprism

instance Member Number t => Member Number (LogicB <: t) where
  uprism = _Tail . uprism
instance Member LogicB t => Member LogicB (Number <: t) where
  uprism = _Tail . uprism

instance Member ArithB t => Member ArithB (LogicB <: t) where
  uprism = _Tail . uprism
instance Member LogicB t => Member LogicB (ArithB <: t) where
  uprism = _Tail . uprism

instance Member CmpB t => Member CmpB (LogicB <: t) where
  uprism = _Tail . uprism
instance Member LogicB t => Member LogicB (CmpB <: t) where
  uprism = _Tail . uprism

showLogicBMPrec
 :: Applicative m
 => (Comp (LogicB <: t) ShowS -> m ShowS)
 -> Comp (LogicB <: t) ShowS -> m ShowS
showLogicBMPrec = showAndMPrec . showOrMPrec
  where
    showOrMPrec, showAndMPrec
     :: Applicative m
     => (Comp (LogicB <: t) ShowS -> m ShowS)
     -> Comp (LogicB <: t) ShowS -> m ShowS
    
    showOrMPrec sp (Req (Head (a :#|| b)) k) =
      showLogicB (showOrMPrec sp (k a) :#|| sp (k b)) id
    showOrMPrec sp m = sp m
  
    showAndMPrec sp (Req (Head (a :#&& b)) k) =
      showLogicB (showAndMPrec sp (k a) :#&& sp (k b)) id
    showAndMPrec sp m = sp m

fromLogicBM :: LogicB_ r => Comp (LogicB <: t) r -> Comp t r
fromLogicBM = handle fromLogicB

-- | Unop
instance Member Unop (Unop <: t) where uprism = _Head

instance Member Comment t => Member Comment (Unop <: t) where
  uprism = _Tail . uprism
instance Member Unop t => Member Unop (Comment <: t) where
  uprism = _Tail . uprism

instance Member Number t => Member Number (Unop <: t) where
  uprism = _Tail . uprism
instance Member Unop t => Member Unop (Number <: t) where
  uprism = _Tail . uprism

instance Member ArithB t => Member ArithB (Unop <: t) where
  uprism = _Tail . uprism
instance Member Unop t => Member Unop (ArithB <: t) where
  uprism = _Tail . uprism

instance Member CmpB t => Member CmpB (Unop <: t) where
  uprism = _Tail . uprism  
instance Member Unop t => Member Unop (CmpB <: t) where
  uprism = _Tail . uprism

showUnopMPrec
 :: Functor m
 => (Comp (Unop <: t) ShowS -> m ShowS)
 -> Comp (Unop <: t) ShowS -> m ShowS
showUnopMPrec = showUnopMPrec' where
  showUnopMPrec' sp (Req (Head h) k) = showUnop h (sp . k)
  showUnopMPrec' sp m = sp m

fromUnopM :: Unop_ r => Comp (Unop <: t) r -> Comp t r
fromUnopM = handle fromUnop

-- | Block
instance Member (Block stmt) (Block stmt <: t) where uprism = _Head
instance MemberU Block (Block s <: t) where
  type UIndex Block (Block s <: t) = s

instance Member Comment t => Member Comment (Block s <: t) where
  uprism = _Tail . uprism
instance Member (Block s) t => Member (Block s) (Comment <: t) where
  uprism = _Tail . uprism
instance MemberU Block t => MemberU Block (Comment <: t) where
  type UIndex Block (Comment <: t) = UIndex Block t

instance Member Number t => Member Number (Block s <: t) where
  uprism = _Tail . uprism
instance Member (Block s) t => Member (Block s) (Number <: t) where
  uprism = _Tail . uprism
instance MemberU Block t => MemberU Block (Number <: t) where
  type UIndex Block (Number <: t) = UIndex Block t

instance Member ArithB t => Member ArithB (Block s <: t) where
  uprism = _Tail . uprism
instance Member (Block s) t => Member (Block s) (ArithB <: t) where
  uprism = _Tail . uprism
instance MemberU Block t => MemberU Block (ArithB <: t) where
  type UIndex Block (ArithB <: t) = UIndex Block t

instance Member CmpB t => Member CmpB (Block s <: t) where
  uprism = _Tail . uprism
instance Member (Block s) t => Member (Block s) (CmpB <: t) where
  uprism = _Tail . uprism
instance MemberU Block t => MemberU Block (CmpB <: t) where
  type UIndex Block (CmpB <: t) = UIndex Block  t

instance Member Unop t => Member Unop (Block s <: t) where
  uprism = _Tail . uprism
instance Member (Block s) t => Member (Block s) (Unop <: t) where
  uprism = _Tail . uprism
instance MemberU Block t => MemberU Block (Unop <: t) where
  type UIndex Block (Unop <: t) = UIndex Block t
  
showBlockM
 :: (forall x . stmt x -> (x -> Comp t ShowS) -> Comp t ShowS)
 -> Comp (Block stmt <: t) ShowS -> Comp t ShowS
showBlockM ss = handle (\ r k -> r `showBlock` (`ss` k))

fromBlockM
 :: Block_ r
 => (forall x . stmt x -> (x -> Comp t r) -> Comp t (Stmt r))
 -> Comp (Block stmt <: t) r -> Comp t r
fromBlockM ks = handle (\ r k -> r `fromBlock` (`ks` k))

-- | Text
instance Member Text (Text <: t) where uprism = _Head

instance Member Comment t => Member Comment (Text <: t) where
  uprism = _Tail . uprism
instance Member Text t => Member Text (Comment <: t) where
  uprism = _Tail . uprism

instance Member Number t => Member Number (Text <: t) where
  uprism = _Tail . uprism
instance Member Text t => Member Text (Number <: t) where
  uprism = _Tail . uprism

instance Member ArithB t => Member ArithB (Text <: t) where
  uprism = _Tail . uprism
instance Member Text t => Member Text (ArithB <: t) where
  uprism = _Tail . uprism

instance Member CmpB t => Member CmpB (Text <: t) where
  uprism = _Tail . uprism
instance Member Text t => Member Text (CmpB <: t) where
  uprism = _Tail . uprism

instance Member LogicB t => Member LogicB (Text <: t) where
  uprism = _Tail . uprism
instance Member Text t => Member Text (LogicB <: t) where
  uprism = _Tail . uprism

instance Member Unop t => Member Unop (Text <: t) where
  uprism = _Tail . uprism
instance Member Text t => Member Text (Unop <: t) where
  uprism = _Tail . uprism

instance Member (Block s) t => Member (Block s) (Text <: t) where
  uprism = _Tail . uprism
instance MemberU Block t => MemberU Block (Text <: t) where
  type UIndex Block (Text <: t) = UIndex Block t
instance Member Text t => Member Text (Block s <: t) where
  uprism = _Tail . uprism

showTextM :: Comp (Text <: t) ShowS -> Comp t ShowS
showTextM = handle (const . pure . showText)

fromTextM :: Text_ r => Comp (Text <: t) r -> Comp t r
fromTextM = handle (const . pure . fromText)

-- | Var
instance Member Var (Var <: t) where uprism = _Head

instance Member Comment t => Member Comment (Var <: t) where
  uprism = _Tail . uprism
instance Member Var t => Member Var (Comment <: t) where
  uprism = _Tail . uprism

instance Member Number t => Member Number (Var <: t) where
  uprism = _Tail . uprism
instance Member Var t => Member Var (Number <: t) where
  uprism = _Tail . uprism

instance Member ArithB t => Member ArithB (Var <: t) where
  uprism = _Tail . uprism
instance Member Var t => Member Var (ArithB <: t) where
  uprism = _Tail . uprism

instance Member CmpB t => Member CmpB (Var <: t) where
  uprism = _Tail . uprism
instance Member Var t => Member Var (CmpB <: t) where
  uprism = _Tail . uprism

instance Member LogicB t => Member LogicB (Var <: t) where
  uprism = _Tail . uprism
instance Member Var t => Member Var (LogicB <: t) where
  uprism = _Tail . uprism

instance Member Unop t => Member Unop (Var <: t) where
  uprism = _Tail . uprism
instance Member Var t => Member Var (Unop <: t) where
  uprism = _Tail . uprism

instance Member (Block s) t => Member (Block s) (Var <: t) where
  uprism = _Tail . uprism
instance MemberU Block t => MemberU Block (Var <: t) where
  type UIndex Block (Var <: t) = UIndex Block t
instance Member Var t => Member Var (Block s <: t) where
  uprism = _Tail . uprism

instance Member Text t => Member Text (Var <: t) where
  uprism = _Tail . uprism
instance Member Var t => Member Var (Text <: t) where
  uprism = _Tail . uprism

showVarM :: Comp (Var <: t) ShowS -> Comp t ShowS
showVarM = handle (const . pure . showVar)

fromVarM :: IsString r => Comp (Var <: t) r -> Comp t r
fromVarM = handle (const . pure . fromVar)

-- | Field
instance Member Field (Field <: t) where uprism = _Head

instance Member Comment t => Member Comment (Field <: t) where
  uprism = _Tail . uprism
instance Member Field t => Member Field (Comment <: t) where
  uprism = _Tail . uprism

instance Member Number t => Member Number (Field <: t) where
  uprism = _Tail . uprism
instance Member Field t => Member Field (Number <: t) where
  uprism = _Tail . uprism

instance Member ArithB t => Member ArithB (Field <: t) where
  uprism = _Tail . uprism
instance Member Field t => Member Field (ArithB <: t) where
  uprism = _Tail . uprism

instance Member CmpB t => Member CmpB (Field <: t) where
  uprism = _Tail . uprism
instance Member Field t => Member Field (CmpB <: t) where
  uprism = _Tail . uprism

instance Member LogicB t => Member LogicB (Field <: t) where
  uprism = _Tail . uprism
instance Member Field t => Member Field (LogicB <: t) where
  uprism = _Tail . uprism

instance Member Unop t => Member Unop (Field <: t) where
  uprism = _Tail . uprism
instance Member Field t => Member Field (Unop <: t) where
  uprism = _Tail . uprism

instance Member (Block s) t => Member (Block s) (Field <: t) where
  uprism = _Tail . uprism
instance MemberU Block t => MemberU Block (Field <: t) where
  type UIndex Block (Field <: t) = UIndex Block t
instance Member Field t => Member Field (Block s <: t) where
  uprism = _Tail . uprism

instance Member Var t => Member Var (Field <: t) where
  uprism = _Tail . uprism
instance Member Field t => Member Field (Var <: t) where
  uprism = _Tail . uprism

showChainM :: Comp (Field <: t) ShowS -> Comp t ShowS
showChainM = handle showField

fromChainM :: Chain_ r => Comp (Field <: t) r -> Comp t r
fromChainM = handle fromField

-- | Extern
instance Member Extern (Extern <: t) where uprism = _Head

instance Member Comment t => Member Comment (Extern <: t) where
  uprism = _Tail . uprism
instance Member Extern t => Member Extern (Comment <: t) where
  uprism = _Tail . uprism

instance Member Number t => Member Number (Extern <: t) where
  uprism = _Tail . uprism
instance Member Extern t => Member Extern (Number <: t) where
  uprism = _Tail . uprism

instance Member ArithB t => Member ArithB (Extern <: t) where
  uprism = _Tail . uprism
instance Member Extern t => Member Extern (ArithB <: t) where
  uprism = _Tail . uprism

instance Member LogicB t => Member LogicB (Extern <: t) where
  uprism = _Tail . uprism
instance Member Extern t => Member Extern (CmpB <: t) where
  uprism = _Tail . uprism

instance Member CmpB t => Member CmpB (Extern <: t) where
  uprism = _Tail . uprism
instance Member Extern t => Member Extern (LogicB <: t) where
  uprism = _Tail . uprism

instance Member Unop t => Member Unop (Extern <: t) where
  uprism = _Tail . uprism
instance Member Extern t => Member Extern (Unop <: t) where
  uprism = _Tail . uprism

instance Member (Block s) t => Member (Block s) (Extern <: t) where
  uprism = _Tail . uprism
instance MemberU Block t => MemberU Block (Extern <: t) where
  type UIndex Block (Extern <: t) = UIndex Block t
instance Member Extern t => Member Extern (Block s <: t) where
  uprism = _Tail . uprism

instance Member Var t => Member Var (Extern <: t) where
  uprism = _Tail . uprism
instance Member Extern t => Member Extern (Var <: t) where
  uprism = _Tail . uprism

instance Member Field t => Member Field (Extern <: t) where
  uprism = _Tail . uprism
instance Member Extern t => Member Extern (Field <: t) where
  uprism = _Tail . uprism

showExternM :: Comp (Extern <: t) ShowS -> Comp t ShowS
showExternM = handle (const . pure . showExtern)

fromExternM :: Extern_ r => Comp (Extern <: t) r -> Comp t r
fromExternM = handle (const . pure . fromExtern)

-- | Extend
instance Member (Extend e) (Extend e <: t) where uprism = _Head
instance MemberU Extend (Extend e <: t) where
  type UIndex Extend (Extend e <: t) = e

instance Member Comment t => Member Comment (Extend e <: t) where
  uprism = _Tail . uprism
instance Member (Extend e) t => Member (Extend e) (Comment <: t) where
  uprism = _Tail . uprism
instance MemberU Extend t => MemberU Extend (Comment <: t) where
  type UIndex Extend (Comment <: t) = UIndex Extend t

instance Member Number t => Member Number (Extend e <: t) where
  uprism = _Tail . uprism
instance Member (Extend e) t => Member (Extend e) (Number <: t) where
  uprism = _Tail . uprism
instance MemberU Extend t => MemberU Extend (Number <: t) where
  type UIndex Extend (Number <: t) = UIndex Extend t

instance Member ArithB t => Member ArithB (Extend e <: t) where
  uprism = _Tail . uprism
instance Member (Extend e) t => Member (Extend e) (ArithB <: t) where
  uprism = _Tail . uprism
instance MemberU Extend t => MemberU Extend (ArithB <: t) where
  type UIndex Extend (ArithB <: t) = UIndex Extend t

instance Member LogicB t => Member LogicB (Extend e <: t) where
  uprism = _Tail . uprism
instance Member (Extend e) t => Member (Extend e) (LogicB <: t) where
  uprism = _Tail . uprism
instance MemberU Extend t => MemberU Extend (LogicB <: t) where
  type UIndex Extend (LogicB <: t) = UIndex Extend t

instance Member CmpB t => Member CmpB (Extend e <: t) where
  uprism = _Tail . uprism
instance Member (Extend e) t => Member (Extend e) (CmpB <: t) where
  uprism = _Tail . uprism
instance MemberU Extend t => MemberU Extend (CmpB <: t) where
  type UIndex Extend (CmpB <: t) = UIndex Extend t

instance Member Unop t => Member Unop (Extend e <: t) where
  uprism = _Tail . uprism
instance Member (Extend e) t => Member (Extend e) (Unop <: t) where
  uprism = _Tail . uprism
instance MemberU Extend t => MemberU Extend (Unop <: t) where
  type UIndex Extend (Unop <: t) = UIndex Extend t

instance Member (Block s) t => Member (Block s) (Extend e <: t) where
  uprism = _Tail . uprism
instance Member (Extend e) t => Member (Extend e) (Block s <: t) where
  uprism = _Tail . uprism
instance MemberU Extend t => MemberU Extend (Block s <: t) where
  type UIndex Extend (Block s <: t) = UIndex Extend t

instance Member Var t => Member Var (Extend e <: t) where
  uprism = _Tail . uprism
instance Member (Extend e) t => Member (Extend e) (Var <: t) where
  uprism = _Tail . uprism
instance MemberU Extend t => MemberU Extend (Var <: t) where
  type UIndex Extend (Var <: t) = UIndex Extend t

instance Member Field t => Member Field (Extend e <: t) where
  uprism = _Tail . uprism
instance Member (Extend e) t => Member (Extend e) (Field <: t) where
  uprism = _Tail . uprism
instance MemberU Extend t => MemberU Extend (Field <: t) where
  type UIndex Extend (Field <: t) = UIndex Extend t

instance Member Extern t => Member Extern (Extend e <: t) where
  uprism = _Tail . uprism
instance Member (Extend e) t => Member (Extend e) (Extern <: t) where
  uprism = _Tail . uprism
instance MemberU Extend t => MemberU Extend (Extern <: t) where
  type UIndex Extend (Extern <: t) = UIndex Extend t

showExtendM
 :: (forall x. ext x -> (x -> Comp t ShowS) -> Comp t ShowS)
 -> Comp (Extend ext <: t) ShowS -> Comp t ShowS
showExtendM sx = handle (showExtend sx)

fromExtendM
 :: Extend_ r
 => (forall x. ext x -> (x -> Comp t r) -> Comp t (Ext r))
 -> Comp (Extend ext <: t) r -> Comp t r
fromExtendM kx = handle (fromExtend kx)
