{-# LANGUAGE RankNTypes, TypeOperators, EmptyCase, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, TypeFamilies, DefaultSignatures #-}
module Goat.Lang.Reflect
  ( module Goat.Comp
  , (<:)(), Null, decomp, _Head, _Tail, handle, handleAll, run, raise
  , showCommentM, fromCommentM
  , showNumberM, fromNumberM
  , showArithBM, fromArithBM, precArithBM
  , showCmpBM, fromCmpBM, precCmpBM
  , showLogicBM, fromLogicBM, precLogicBM
  , showUnopM, fromUnopM, precUnopM
  , showBlockM, fromBlockM
  , showTextM, fromTextM
  , showVarM, fromVarM
  , showFieldM, fromFieldM
  , showExternM, fromExternM
  , showExtendM, fromExtendM
  , showLetM, fromLetM
  , showImportsM, fromImportsM
  , showIncludeM, fromIncludeM
  , showModuleM, fromModuleM
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
import Goat.Lang.Let
import Goat.Lang.Module
import Control.Monad (join)
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
  comp Done (\ r k -> either f Req (decomp r) k)

handleAll
 :: (Comp r a -> Comp Null a) -> Comp r Void -> a
handleAll f = run . f . vacuous

run :: Comp Null a -> a
run = comp id (\ a _ -> case a of {})

class Member h (h' <: t) => Commute h h' t where
  uprism' :: Prism' ((h' <: t) a) (h a)
  default uprism' :: Member h t => Prism' ((h' <: t) a) (h a)
  uprism' = _Tail . uprism
instance Commute h h' t => Member h (h' <: t) where uprism = uprism'

class MemberU tag (h <: t) => CommuteU tag h t where
  type UIndex' tag h t
  type UIndex' tag h t = UIndex tag t
instance CommuteU tag h t => MemberU tag (h <: t) where
  type UIndex tag (h <: t) = UIndex' tag h t

class MemberU2 tag (h <: t) => CommuteU2 tag h t where
  type U1Index' tag h t
  type U1Index' tag h t = U1Index tag t
  type U2Index' tag h t
  type U2Index' tag  h t = U2Index tag t
instance CommuteU2 tag h t => MemberU2 tag (h <: t) where
  type U1Index tag (h <: t) = U1Index' tag h t
  type U2Index tag (h <: t) = U2Index' tag h t


-- | Comment  
showCommentM :: Comp (Comment <: t) ShowS -> Comp t ShowS
showCommentM = handle showComment

fromCommentM
 :: Comment_ r => Comp (Comment <: t) r -> Comp t r
fromCommentM = handle fromComment

instance Commute Comment Comment t where uprism' = _Head

-- | Number
showNumberM :: Comp (Number <: t) ShowS -> Comp t ShowS
showNumberM = handle (const . pure . showNumber)

fromNumberM :: Fractional r => Comp (Number <: t) r -> Comp t r
fromNumberM = handle (const . pure . fromNumber)

instance Commute Number Number t where uprism' = _Head

instance Member Comment t => Commute Comment Number t
instance Member Number t => Commute Number Comment t

-- | ArithB
precArithBM
 :: Member ArithB r
 => (Comp r a -> Comp r a) -> Comp r a -> Comp r a
precArithBM sp = precAddM (precMulM (precPowM sp))
  where
    precAddM, precMulM, precPowM
     :: Member ArithB r
     => (Comp r a -> Comp r a) -> Comp r a -> Comp r a
    precAddM hprec (Req r k) = case prj r of
      Just (a :#+ b) ->
        join (send (hprec (k a) :#+ precAddM hprec (k b)))
      Just (a :#- b) ->
        join (send (hprec (k a) :#- precAddM hprec (k b)))
      Nothing -> hprec (Req r k)
    
    precMulM hprec (Req r k) = case prj r of 
      Just (a :#* b) ->
        join (send (hprec (k a) :#* precMulM hprec (k b)))
      Just (a :#/ b) ->
        join (send (hprec (k a) :#* precMulM hprec (k b)))
      Nothing -> hprec (Req r k)
    
    precPowM hprec (Req r k) = case prj r of
      Just (a :#^ b) ->
        join (send (precPowM hprec (k a) :#^ hprec (k b)))
      Nothing -> hprec (Req r k)

showArithBM
 :: Comp (ArithB <: t) ShowS -> Comp t ShowS
showArithBM = handle showArithB

fromArithBM :: ArithB_ r => Comp (ArithB <: t) r -> Comp t r
fromArithBM = handle fromArithB

instance Commute ArithB ArithB t where uprism' = _Head

instance Member Comment t => Commute Comment ArithB t
instance Member ArithB t => Commute ArithB Comment t

instance Member Number t => Commute Number ArithB t
instance Member ArithB t => Commute ArithB Number t

-- | CmpB
precCmpBM
 :: Member CmpB r
 => (Comp r a -> Comp r a) -> Comp r a -> Comp r a 
precCmpBM = precCmpBM'
  where
    precCmpBM'
     :: Member CmpB r
     => (Comp r a -> Comp r a) -> Comp r a -> Comp r a
    precCmpBM' hprec (Req r k) = case prj r of
      Just (a :#== b) -> hdl (:#==) a b
      Just (a :#!= b) -> hdl (:#!=) a b
      Just (a :#>  b) -> hdl (:#>) a b
      Just (a :#>= b) -> hdl (:#>=) a b
      Just (a :#<  b) -> hdl (:#<) a b
      Just (a :#<= b) -> hdl (:#<=) a b
      Nothing         -> hprec (Req r k)
      where
        hdl op a b = send (a `op` b) >>= hprec . k

showCmpBM :: Comp (CmpB <: t) ShowS -> Comp t ShowS
showCmpBM = handle showCmpB

fromCmpBM
 :: CmpB_ r => Comp (CmpB <: t) r -> Comp t r
fromCmpBM = handle fromCmpB

instance Commute CmpB CmpB t where uprism' = _Head

instance Member Comment t => Commute Comment CmpB t
instance Member CmpB t => Commute CmpB Comment t

instance Member Number t => Commute Number CmpB t
instance Member CmpB t => Commute CmpB Number t

instance Member ArithB t => Commute ArithB CmpB t
instance Member CmpB t => Commute CmpB ArithB t


-- | LogicB
precLogicBM
 :: Member LogicB r
 => (Comp r a -> Comp r a) -> Comp r a -> Comp r a
precLogicBM hprec = precAndM (precOrM hprec)
  where
    precOrM, precAndM
     :: Member LogicB r
     => (Comp r a -> Comp r a) -> Comp r a -> Comp r a
    precOrM hprec (Req r k) = case prj r of
      Just (a :#|| b) ->
        join (send (precOrM hprec (k a) :#|| hprec (k b)))
      Nothing -> hprec (Req r k)
  
    precAndM hprec (Req r k) = case prj r of
      Just (a :#&& b) ->
        join (send (precAndM hprec (k a) :#&& hprec (k b)))
      Nothing -> hprec (Req r k)
    
showLogicBM
 :: Comp (LogicB <: t) ShowS -> Comp t ShowS
showLogicBM = handle showLogicB

fromLogicBM :: LogicB_ r => Comp (LogicB <: t) r -> Comp t r
fromLogicBM = handle fromLogicB

instance Commute LogicB LogicB t where uprism' = _Head

instance Member Comment t => Commute Comment LogicB t
instance Member LogicB t => Commute LogicB Comment t

instance Member Number t => Commute Number LogicB t
instance Member LogicB t => Commute LogicB Number t

instance Member ArithB t => Commute ArithB LogicB t
instance Member LogicB t => Commute LogicB ArithB t

instance Member CmpB t => Commute CmpB LogicB t
instance Member LogicB t => Commute LogicB CmpB t

-- | Unop
precUnopM
 :: Member Unop r
 => (Comp r a -> Comp r a) -> Comp r a -> Comp r a
precUnopM = precUnopM' where
  precUnopM'
   :: Member Unop r
   => (Comp r a -> Comp r a) -> Comp r a -> Comp r a
  precUnopM' hprec (Req r k) = case prj r of
    Just (NegU a) -> send (NegU a) >>= hprec . k
    Just (NotU a) -> send (NotU a) >>= hprec . k
    Nothing -> hprec (Req r k)

showUnopM
 :: Comp (Unop <: t) ShowS -> Comp t ShowS
showUnopM = handle showUnop

fromUnopM :: Unop_ r => Comp (Unop <: t) r -> Comp t r
fromUnopM = handle fromUnop

instance Commute Unop Unop t where uprism' = _Head

instance Member Comment t => Commute Comment Unop t
instance Member Unop t => Commute Unop Comment t

instance Member Number t => Commute Number Unop t
instance Member Unop t => Commute Unop Number t

instance Member ArithB t => Commute ArithB Unop t
instance Member Unop t => Commute Unop ArithB t

instance Member CmpB t => Commute CmpB Unop t
instance Member Unop t => Commute Unop CmpB t

instance Member LogicB t => Commute LogicB Unop t
instance Member Unop t => Commute Unop LogicB t

-- | Block
showBlockM
 :: (stmt -> Comp t ShowS)
 -> Comp (Block stmt <: t) ShowS -> Comp t ShowS
showBlockM ss = handle (\ r _ -> showBlock ss r)

fromBlockM
 :: Block_ r
 => (stmt -> Comp t (Stmt r))
 -> Comp (Block stmt <: t) r -> Comp t r
fromBlockM ks = handle (\ r _ -> fromBlock ks r)

instance Commute (Block stmt) (Block stmt) t where uprism' = _Head
instance CommuteU Block (Block s) t where
  type UIndex' Block (Block s) t = s

instance Member Comment t => Commute Comment (Block s) t
instance Member (Block s) t => Commute (Block s) Comment t
instance MemberU Block t => CommuteU Block Comment t

instance Member Number t => Commute Number (Block s) t
instance Member (Block s) t => Commute (Block s) Number t
instance MemberU Block t => CommuteU Block Number t

instance Member ArithB t => Commute ArithB (Block s) t
instance Member (Block s) t => Commute (Block s) ArithB t
instance MemberU Block t => CommuteU Block ArithB t

instance Member CmpB t => Commute CmpB (Block s) t
instance Member (Block s) t => Commute (Block s) CmpB t
instance MemberU Block t => CommuteU Block CmpB t

instance Member LogicB t => Commute LogicB (Block s) t
instance Member (Block s) t => Commute (Block s) LogicB t
instance MemberU Block t => CommuteU Block LogicB t

instance Member Unop t => Commute Unop (Block s) t
instance Member (Block s) t => Commute (Block s) Unop t
instance MemberU Block t => CommuteU Block Unop t

-- | Text
showTextM :: Comp (Text <: t) ShowS -> Comp t ShowS
showTextM = handle (const . pure . showText)

fromTextM :: Text_ r => Comp (Text <: t) r -> Comp t r
fromTextM = handle (const . pure . fromText)

instance Commute Text Text t where uprism' = _Head

instance Member Comment t => Commute Comment Text t
instance Member Text t => Commute Text Comment t

instance Member Number t => Commute Number Text t
instance Member Text t => Commute Text Number t

instance Member ArithB t => Commute ArithB Text t
instance Member Text t => Commute Text ArithB t

instance Member CmpB t => Commute CmpB Text t
instance Member Text t => Commute Text CmpB t

instance Member LogicB t => Commute LogicB Text t
instance Member Text t => Commute Text LogicB t

instance Member Unop t => Commute Unop Text t
instance Member Text t => Commute Text Unop t

instance Member (Block s) t => Commute (Block s) Text t
instance MemberU Block t => CommuteU Block Text t
instance Member Text t => Commute Text (Block s) t

-- | Var
showVarM :: Comp (Var <: t) ShowS -> Comp t ShowS
showVarM = handle (const . pure . showVar)

fromVarM :: IsString r => Comp (Var <: t) r -> Comp t r
fromVarM = handle (const . pure . fromVar)

instance Commute Var Var t where uprism' = _Head

instance Member Comment t => Commute Comment Var t
instance Member Var t => Commute Var Comment t

instance Member Number t => Commute Number Var t
instance Member Var t => Commute Var Number t

instance Member ArithB t => Commute ArithB Var t
instance Member Var t => Commute Var ArithB t

instance Member CmpB t => Commute CmpB Var t
instance Member Var t => Commute Var CmpB t

instance Member LogicB t => Commute LogicB Var t
instance Member Var t => Commute Var LogicB t

instance Member Unop t => Commute Unop Var t
instance Member Var t => Commute Var Unop t

instance Member (Block s) t => Commute (Block s) Var t
instance MemberU Block t => CommuteU Block Var t
instance Member Var t => Commute Var (Block s) t

instance Member Text t => Commute Text Var t
instance Member Var t => Commute Var Text t

-- | Field
showFieldM 
 :: (cmp -> Comp t ShowS)
 -> Comp (Field cmp <: t) ShowS -> Comp t ShowS
showFieldM sc = handle (\ r _ -> showField sc r)

fromFieldM
 :: Field_ r
 => (cmp -> Comp t (Compound r))
 -> Comp (Field cmp <: t) r -> Comp t r
fromFieldM kc = handle (\ r _ -> fromField kc r)

instance Commute (Field c) (Field c) t where uprism' = _Head
instance CommuteU Field (Field c) t where
  type UIndex' Field (Field c) t = c

instance Member Comment t => Commute Comment (Field c) t
instance Member (Field c) t => Commute (Field c) Comment t
instance MemberU Field t => CommuteU Field Comment t

instance Member Number t => Commute Number (Field c) t
instance Member (Field c) t => Commute (Field c) Number t
instance MemberU Field t => CommuteU Field Number t

instance Member ArithB t => Commute ArithB (Field c) t
instance Member (Field c) t => Commute (Field c) ArithB t
instance MemberU Field t => CommuteU Field ArithB t

instance Member CmpB t => Commute CmpB (Field c) t
instance Member (Field c) t => Commute (Field c) CmpB t
instance MemberU Field t => CommuteU Field CmpB t

instance Member LogicB t => Commute LogicB (Field c) t
instance Member (Field c) t => Commute (Field c) LogicB t
instance MemberU Field t => CommuteU Field LogicB t

instance Member Unop t => Commute Unop (Field c) t
instance Member (Field c) t => Commute (Field c) Unop t
instance MemberU Field t => CommuteU Field Unop t

instance Member (Block s) t => Commute (Block s) (Field c) t
instance MemberU Block t => CommuteU Block (Field c) t
instance Member (Field c) t => Commute (Field c) (Block s) t
instance MemberU Field t => CommuteU Field (Block s) t

instance Member Text t => Commute Text (Field c) t
instance Member (Field c) t => Commute (Field c) Text t
instance MemberU Field t => CommuteU Field Text t

instance Member Var t => Commute Var (Field c) t
instance Member (Field c) t => Commute (Field c) Var t
instance MemberU Field t => CommuteU Field Var t

-- | Extern
showExternM :: Comp (Extern <: t) ShowS -> Comp t ShowS
showExternM = handle (const . pure . showExtern)

fromExternM :: Extern_ r => Comp (Extern <: t) r -> Comp t r
fromExternM = handle (const . pure . fromExtern)

instance Commute Extern Extern t where uprism' = _Head

instance Member Comment t => Commute Comment Extern t
instance Member Extern t => Commute Extern Comment t

instance Member Number t => Commute Number Extern t
instance Member Extern t => Commute Extern Number t

instance Member ArithB t => Commute ArithB Extern t
instance Member Extern t => Commute Extern ArithB t

instance Member LogicB t => Commute LogicB Extern t
instance Member Extern t => Commute Extern CmpB t

instance Member CmpB t => Commute CmpB Extern t
instance Member Extern t => Commute Extern LogicB t

instance Member Unop t => Commute Unop Extern t
instance Member Extern t => Commute Extern Unop t

instance Member (Block s) t => Commute (Block s) Extern t
instance MemberU Block t => CommuteU Block Extern t
instance Member Extern t => Commute Extern (Block s) t

instance Member Text t => Commute Text Extern t
instance Member Extern t => Commute Extern Text t

instance Member Var t => Commute Var Extern t
instance Member Extern t => Commute Extern Var t

instance Member (Field c) t => Commute (Field c) Extern t
instance MemberU Field t => CommuteU Field Extern t
instance Member Extern t => Commute Extern (Field c) t

-- | Extend
showExtendM
 :: (ext -> Comp t ShowS) 
 -> (extn -> Comp t ShowS)
 -> Comp (Extend ext extn <: t) ShowS
 -> Comp t ShowS
showExtendM se sx = handle (\ r _ -> showExtend se sx r)

fromExtendM
 :: Extend_ r
 => (ext -> Comp t (Ext r))
 -> (extn -> Comp t (Extension r))
 -> Comp (Extend ext extn <: t) r
 -> Comp t r
fromExtendM ke kx = handle (\ r _ -> fromExtend ke kx r)

instance Commute (Extend e x) (Extend e x) t where uprism' = _Head
instance CommuteU2 Extend (Extend e x) t where
  type U1Index' Extend (Extend e x) t = x
  type U2Index' Extend (Extend e x) t = e

instance Member Comment t => Commute Comment (Extend e x) t
instance Member (Extend e x) t => Commute (Extend e x) Comment t
instance MemberU2 Extend t => CommuteU2 Extend Comment t

instance Member Number t => Commute Number (Extend e x) t
instance Member (Extend e x) t => Commute (Extend e x) Number t
instance MemberU2 Extend t => CommuteU2 Extend Number t

instance Member ArithB t => Commute ArithB (Extend e x) t
instance Member (Extend e x) t => Commute (Extend e x) ArithB t
instance MemberU2 Extend t => CommuteU2 Extend ArithB t

instance Member LogicB t => Commute LogicB (Extend e x) t
instance Member (Extend e x) t => Commute (Extend e x) LogicB t
instance MemberU2 Extend t => CommuteU2 Extend LogicB t

instance Member CmpB t => Commute CmpB (Extend e x) t
instance Member (Extend e x) t => Commute (Extend e x) CmpB t
instance MemberU2 Extend t => CommuteU2 Extend CmpB t

instance Member Unop t => Commute Unop (Extend e x) t
instance Member (Extend e x) t => Commute (Extend e x) Unop t
instance MemberU2 Extend t => CommuteU2 Extend Unop t

instance Member (Block s) t => Commute (Block s) (Extend e x) t
instance MemberU Block t => CommuteU Block (Extend e x) t
instance Member (Extend e x) t => Commute (Extend e x) (Block s) t
instance MemberU2 Extend t => CommuteU2 Extend (Block s) t

instance Member Text t => Commute Text (Extend e x) t
instance Member (Extend e x) t => Commute (Extend e x) Text t
instance MemberU2 Extend t => CommuteU2 Extend Text t

instance Member Var t => Commute Var (Extend e x) t
instance Member (Extend e x) t => Commute (Extend e x) Var t
instance MemberU2 Extend t => CommuteU2 Extend Var t

instance Member (Field c) t => Commute (Field c) (Extend e x) t
instance MemberU Field t => CommuteU Field (Extend e x) t
instance Member (Extend e x) t => Commute (Extend e x) (Field c) t
instance MemberU2 Extend t => CommuteU2 Extend (Field c) t

instance Member Extern t => Commute Extern (Extend e x) t
instance Member (Extend e x) t => Commute (Extend e x) Extern t
instance MemberU2 Extend t => CommuteU2 Extend Extern t

-- | Let
showLetM
 :: (l -> Comp t ShowS)
 -> (r -> Comp t ShowS)
 -> Comp (Let l r <: t) ShowS -> Comp t ShowS
showLetM sl sr = handle (\ r _ -> showLet sl sr r)

fromLetM
 :: Let_ s
 => (lhs -> Comp t (Lhs s))
 -> (rhs -> Comp t (Rhs s))
 -> Comp (Let lhs rhs <: t) s -> Comp t s
fromLetM kl kr = handle (\ r _ -> fromLet kl kr r)

instance Commute (Let l r) (Let l r) t where uprism' = _Head
instance CommuteU2 Let (Let l r) t where
  type U2Index' Let (Let l r) t = l
  type U1Index' Let (Let l r) t = r

instance Member Comment t => Commute Comment (Let l r) t
instance Member (Let l r) t => Commute (Let l r) Comment t
instance MemberU2 Let t => CommuteU2 Let Comment t

instance Member Number t => Commute Number (Let l r) t
instance Member (Let l r) t => Commute (Let l r) Number t
instance MemberU2 Let t => CommuteU2 Let Number t

instance Member ArithB t => Commute ArithB (Let l r) t
instance Member (Let l r) t => Commute (Let l r) ArithB t
instance MemberU2 Let t => CommuteU2 Let ArithB t

instance Member CmpB t => Commute CmpB (Let l r) t
instance Member (Let l r) t => Commute (Let l r) CmpB t
instance MemberU2 Let t => CommuteU2 Let CmpB t

instance Member LogicB t => Commute LogicB (Let l r) t
instance Member (Let l r) t => Commute (Let l r) LogicB t
instance MemberU2 Let t => CommuteU2 Let LogicB t

instance Member Unop t => Commute Unop (Let l r) t
instance Member (Let l r) t => Commute (Let l r) Unop t
instance MemberU2 Let t => CommuteU2 Let Unop t

instance Member (Block s) t => Commute (Block s) (Let l r) t
instance MemberU Block t => CommuteU Block (Let l r) t
instance Member (Let l r) t => Commute (Let l r) ((Block s)) t
instance MemberU2 Let t => CommuteU2 Let ((Block s)) t

instance Member Text t => Commute Text (Let l r) t
instance Member (Let l r) t => Commute (Let l r) Text t
instance MemberU2 Let t => CommuteU2 Let Text t

instance Member Var t => Commute Var (Let l r) t
instance Member (Let l r) t => Commute (Let l r) Var t
instance MemberU2 Let t => CommuteU2 Let Var t

instance Member (Field c) t => Commute (Field c) (Let l r) t
instance MemberU Field t => CommuteU Field (Let l r) t
instance Member (Let l r) t => Commute (Let l r) (Field c) t
instance MemberU2 Let t => CommuteU2 Let (Field c) t

instance Member Extern t => Commute Extern (Let l r) t
instance Member (Let l r) t => Commute (Let l r) Extern t
instance MemberU2 Let t => CommuteU2 Let Extern t

instance Member (Extend e x) t => Commute (Extend e x) (Let l r) t
instance MemberU2 Extend t => CommuteU2 Extend (Let l r) t
instance Member (Let l r) t => Commute (Let l r) (Extend e x) t
instance MemberU2 Let t => CommuteU2 Let (Extend e x) t

-- | Imports
showImportsM
 :: (is -> Comp t ShowS)
 -> (i -> Comp t ShowS)
 -> Comp (Imports is i <: t) ShowS -> Comp t ShowS
showImportsM ss si = handle (\ r _ -> showImports ss si r)

fromImportsM
 :: Imports_ r
 => (is -> Comp t (ImportStmt r))
 -> (i -> Comp t (Imp r))
 -> Comp (Imports is i <: t) r -> Comp t r
fromImportsM ks ki = handle (\ r _ -> fromImports ks ki r)

instance Commute (Imports is i) (Imports is i) t where
  uprism' = _Head
instance CommuteU2 Imports (Imports is i) t where
  type U1Index' Imports (Imports is i) t = i
  type U2Index' Imports (Imports is i) t = is

instance Member Comment t => Commute Comment (Imports is i) t
instance Member (Imports is i) t => Commute (Imports is i) Comment t
instance MemberU2 Imports t => CommuteU2 Imports Comment t

instance Member Number t => Commute Number (Imports is i) t
instance Member (Imports is i) t => Commute (Imports is i) Number t
instance MemberU2 Imports t => CommuteU2 Imports Number t

instance Member ArithB t => Commute ArithB (Imports is i) t
instance Member (Imports is i) t => Commute (Imports is i) ArithB t
instance MemberU2 Imports t => CommuteU2 Imports ArithB t

instance Member CmpB t => Commute CmpB (Imports is i) t
instance Member (Imports is i) t => Commute (Imports is i) CmpB t
instance MemberU2 Imports t => CommuteU2 Imports CmpB t

instance Member LogicB t => Commute LogicB (Imports s i) t
instance Member (Imports is i) t => Commute (Imports is i) LogicB t
instance MemberU2 Imports t => CommuteU2 Imports LogicB t

instance Member Text t => Commute Text (Imports is i) t
instance Member (Imports is i) t => Commute (Imports is i) Text t
instance MemberU2 Imports t => CommuteU2 Imports Text t

instance Member Var t => Commute Var (Imports is i) t
instance Member (Imports is i) t => Commute (Imports is i) Var t
instance MemberU2 Imports t => CommuteU2 Imports Var t

instance Member (Block s) t => Commute (Block s) (Imports is i) t
instance Member (Imports is i) t => Commute (Imports is i) (Block s) t
instance MemberU2 Imports t => CommuteU2 Imports (Block s) t

instance Member (Field c) t => Commute (Field c) (Imports is i) t
instance Member (Imports is i) t => Commute (Imports is i) (Field c) t
instance MemberU2 Imports t => CommuteU2 Imports (Field c) t

instance Member Extern t => Commute Extern (Imports is i) t
instance Member (Imports is i) t => Commute (Imports is i) Extern t
instance MemberU2 Imports t => CommuteU2 Imports Extern t

instance
  Member (Extend e x) t => Commute (Extend e x) (Imports is i) t
instance MemberU2 Extend t => CommuteU2 Extend (Imports is i) t
instance
  Member (Imports is i) t => Commute (Imports is i) (Extend e x) t
instance MemberU2 Imports t => CommuteU2 Imports (Extend e x) t

instance Member (Let l r) t => Commute (Let l r) (Imports is i) t
instance Member (Imports is i) t => Commute (Imports is i) (Let l r) t
instance MemberU2 Imports t => CommuteU2 Imports (Let l r) t

-- | Include
showIncludeM
 :: (n -> Comp t ShowS)
 -> Comp (Include n <: t) ShowS -> Comp t ShowS
showIncludeM sn = handle (\ r _ -> showInclude sn r)

fromIncludeM
 :: Include_ r
 => (inc -> Comp t (Inc r))
 -> Comp (Include inc <: t) r -> Comp t r
fromIncludeM kn = handle (\ r _ -> fromInclude kn r)

instance Commute (Include n) (Include n) t where uprism' = _Head
instance CommuteU Include (Include n) t where
  type UIndex' Include (Include n) t = n

instance Member Comment t => Commute Comment (Include n) t
instance Member (Include n) t => Commute (Include n) Comment t
instance MemberU Include t => CommuteU Include Comment t

instance Member Number t => Commute Number (Include n) t
instance Member (Include n) t => Commute (Include n) Number t
instance MemberU Include t => CommuteU Include Number t

instance Member ArithB t => Commute ArithB (Include n) t
instance Member (Include n) t => Commute (Include n) ArithB t
instance MemberU Include t => CommuteU Include ArithB t

instance Member CmpB t => Commute CmpB (Include n) t
instance Member (Include n) t => Commute (Include n) CmpB t
instance MemberU Include t => CommuteU Include CmpB t

instance Member LogicB t => Commute LogicB (Include n) t
instance Member (Include n) t => Commute (Include n) LogicB t
instance MemberU Include t => CommuteU Include LogicB t

instance Member Unop t => Commute Unop (Include n) t
instance Member (Include n) t => Commute (Include n) Unop t
instance MemberU Include t => CommuteU Include Unop t

instance Member (Block s) t => Commute (Block s) (Include n) t
instance MemberU Block t => CommuteU Block (Include n) t
instance Member (Include n) t => Commute (Include n) (Block s) t
instance MemberU Include t => CommuteU Include (Block s) t

instance Member Text t => Commute Text (Include n) t
instance Member (Include n) t => Commute (Include n) Text t
instance MemberU Include t => CommuteU Include Text t

instance Member Var t => Commute Var (Include n) t
instance Member (Include n) t => Commute (Include n) Var t
instance MemberU Include t => CommuteU Include Var t

instance Member (Field c) t => Commute (Field c) (Include n) t
instance MemberU Field t => CommuteU Field (Include n) t
instance Member (Include n) t => Commute (Include n) (Field c) t
instance MemberU Include t => CommuteU Include (Field c) t

instance Member Extern t => Commute Extern (Include n) t
instance Member (Include n) t => Commute (Include n) Extern t
instance MemberU Include t => CommuteU Include Extern t

instance Member (Extend e x) t => Commute (Extend e x) (Include n) t
instance MemberU2 Extend t => CommuteU2 Extend (Include n) t
instance Member (Include n) t => Commute (Include n) (Extend e x) t
instance MemberU Include t => CommuteU Include (Extend e x) t

instance Member (Let l r) t => Commute (Let l r) (Include n) t
instance MemberU2 Let t => CommuteU2 Let (Include n) t
instance Member (Include n) t => Commute (Include n) (Let l r) t
instance MemberU Include t => CommuteU Include (Let l r) t

instance
  Member (Imports si i) t => Commute (Imports si i) (Include n) t
instance MemberU2 Imports t => CommuteU2 Imports (Include n) t
instance Member (Include n) t => Commute (Include n) (Imports si i) t
instance MemberU Include t => CommuteU Include (Imports si i) t

-- | Module
showModuleM
 :: (ms -> Comp t ShowS)
 -> Comp (Module ms <: t) ShowS -> Comp t ShowS
showModuleM ss = handle (\ r _ -> showModule ss r)

fromModuleM
 :: Module_ r
 => (mstmt -> Comp t (ModuleStmt r))
 -> Comp (Module mstmt <: t) r -> Comp t r
fromModuleM ks = handle (\ r _ -> fromModule ks r)

instance Commute (Module ms) (Module ms) t where uprism' = _Head
instance CommuteU Module (Module ms) t where
  type UIndex' Module (Module ms) t = ms

instance Member Comment t => Commute Comment (Module ms) t
instance Member (Module ms) t => Commute (Module ms) Comment t
instance MemberU Module t => CommuteU Module Comment t

instance Member Number t => Commute Number (Module ms) t
instance Member (Module ms) t => Commute (Module ms) Number t
instance MemberU Module t => CommuteU Module Number t

instance Member ArithB t => Commute ArithB (Module ms) t
instance Member (Module ms) t => Commute (Module ms) ArithB t
instance MemberU Module t => CommuteU Module ArithB t

instance Member CmpB t => Commute CmpB (Module ms) t
instance Member (Module ms) t => Commute (Module ms) CmpB t
instance MemberU Module t => CommuteU Module CmpB t

instance Member LogicB t => Commute LogicB (Module ms) t
instance Member (Module ms) t => Commute (Module ms) LogicB t
instance MemberU Module t => CommuteU Module LogicB t

instance Member Unop t => Commute Unop (Module ms) t
instance Member (Module ms) t => Commute (Module ms) Unop t
instance MemberU Module t => CommuteU Module Unop t

instance Member (Block s) t => Commute (Block s) (Module ms) t
instance MemberU Block t => CommuteU Block (Module ms) t
instance Member (Module ms) t => Commute (Module ms) (Block s) t
instance MemberU Module t => CommuteU Module (Block s) t

instance Member Text t => Commute Text (Module ms) t
instance Member (Module ms) t => Commute (Module ms) Text t
instance MemberU Module t => CommuteU Module Text t

instance Member Var t => Commute Var (Module ms) t
instance Member (Module ms) t => Commute (Module ms) Var t
instance MemberU Module t => CommuteU Module Var t

instance Member (Field c) t => Commute (Field c) (Module ms) t
instance MemberU Field t => CommuteU Field (Module ms) t
instance Member (Module ms) t => Commute (Module ms) (Field c) t
instance MemberU Module t => CommuteU Module (Field c) t

instance Member Extern t => Commute Extern (Module ms) t
instance Member (Module ms) t => Commute (Module ms) Extern t
instance MemberU Module t => CommuteU Module Extern t

instance Member (Extend e x) t => Commute (Extend e x) (Module ms) t
instance MemberU2 Extend t => CommuteU2 Extend (Module ms) t
instance Member (Module ms) t => Commute (Module ms) (Extend e x) t
instance MemberU Module t => CommuteU Module (Extend e x) t

instance Member (Let l r) t => Commute (Let l r) (Module ms) t
instance MemberU2 Let t => CommuteU2 Let (Module ms) t
instance Member (Module ms) t => Commute (Module ms) (Let l r) t
instance MemberU Module t => CommuteU Module (Let l r) t

instance
  Member (Imports si i) t => Commute (Imports si i) (Module ms) t
instance
  MemberU2 Imports t => CommuteU2 Imports (Module ms) t
instance Member (Module ms) t => Commute (Module ms) (Imports si i) t
instance MemberU Module t => CommuteU Module (Imports si i) t

instance Member (Include n) t => Commute (Include n) (Module ms) t
instance MemberU Include t => CommuteU Include (Module ms) t
instance Member (Module ms) t => Commute (Module ms) (Include n) t
instance MemberU Module t => CommuteU Module (Include n) t
