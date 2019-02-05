{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, ConstraintKinds #-}
--{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Goat.Syntax.Extend
  where

import Goat.Syntax.Block
  ( Block_(..), Block(..), fromBlock, showBlock )
import Goat.Syntax.Field
  ( Field_(..), Path_, Path(..), fromPath, showPath
  , Chain_, Chain(..)
  )
import Goat.Syntax.Let
 ( Let_(..), showLet
 , Pun_, Pun, fromPun, parsePun, showPun
 )
import Text.Parsec.Text (Parser)
import Data.String (IsString(..))

infixl 9 #, :#

-- | Parse a value extension
class Extend_ r where
  type Ext r
  (#) :: r -> Ext r -> r

parseExtend :: Extend_ r => Parser (r -> Ext r -> r)
parseExtend = pure (#)

data Extend ext a = a :# ext deriving (Eq, Show)

instance Extend_ (Comp (Extend ext <: k) a) where
  type Ext (Comp (Extend ext <: k) a) = ext
  a # x = send (a :# x)

instance Block_ (Comp k a)
 => Block_ (Comp (Extend ext <: k) a) where
  type Stmt (Comp (Extend ext <: k) a) = Stmt (Comp k a)
  block_ sbdy = inj (block_ sbdy)

instance Field_ (Comp k a)
 => Field_ (Comp (Extend ext <: k) a) where
  type Compound (Comp (Extend ext <: k) a) = Compound (Comp k a)
  c #. i = inj (c #. i)

showExtend
 :: (ext -> ShowS)
 -> Comp (Extend ext <: k) ShowS -> Comp k ShowS
showExtend sx = handle (\ (ex :# x) k -> do
  s <- k ex
  return (s . sx x))

fromExtend
 :: Extend_ r
 => (x -> Ext r)
 -> Comp (Extend x <: k) r -> Comp k r
fromExtend kx = handle (\ (ex :# x) k -> do
  ex' <- k ex
  return (ex' # kx x))


-- | Create or extend a value with a literal block
type ExtendBlock stmt ext a =
  Extend (Block stmt ext) (Block stmt a)

type ExtendBlock_ r =
  ( Block_ r, Extend_ r, Block_ (Ext r), Stmt (Ext r) ~ Stmt r )
  -- r, Stmt r, Ext r, Stmt (Ext r)

showExtendBlock
 :: (stmt -> ShowS)
 -> (ext -> ShowS)
 -> (a -> ShowS)
 -> ExtendBlock stmt ext a -> ShowS
showExtendBlock ss sx sa =
  showExtend (showBlock ss sx) (showBlock ss sa)
  
fromExtendBlock
 :: ExtendBlock_ r
 => (stmt -> Stmt r)
 -> (ext -> Ext r)
 -> (a -> r)
 -> ExtendBlock stmt ext a -> r
fromExtendBlock ks kx ka =
  fromExtend (fromBlock ks kx) (fromBlock ks ka)
  
-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
-- * Let path pattern (leaf pattern assigns matched value to path)
-- * Block pattern (matches a set of paths to nested (lifted) patterns)
-- * An block pattern with left over pattern (matches set of fields not
--   matched by the block pattern)
newtype Patt lcmp lhs scmp stmt ext cmp a =
  Patt
    (ExtendBlock
      (Pun
        lcmp
        lhs
        (Patt lcmp lhs scmp stmt ext cmp a)
        scmp
        stmt)
      ext
      (Path cmp a))

type Patt_ p =
  ( Path_ p, ExtendBlock_ p, Pun_ (Stmt p), Rhs (Stmt p) ~ p )
  -- p, Compound p, Stmt p, Ext p, Lhs (Stmt p), Rhs (Stmt p), Compound (Lhs (Stmt p))
  
instance Field_ (Patt lcmp lhs scmp stmt ext cmp a) where
  type Compound (Patt lcmp lhs scmp stmt ext cmp a) =
    Compound (Path cmp a)
  c #. i = Patt (c #. i)

instance Extend_ (Patt lcmp lhs scmp stmt ext cmp a) where
  type Ext (Patt lcmp lhs scmp stmt ext cmp a) =
    Block
      (Pun
        lcmp
        lhs
        (Patt lcmp lhs scmp stmt ext cmp a)
        scmp
        stmt)
      ext
  Patt ex # x = Patt (ex # x)
  
instance Block_ (Patt lcmp lhs scmp stmt ext cmp a) where
  type Stmt (Patt lcmp lhs scmp stmt ext cmp a) =
    Pun lcmp lhs (Patt lcmp lhs scmp stmt ext cmp a) scmp stmt
  block_ = Patt . block_

showPatt
 :: (lcmp -> ShowS)
 -> (lhs -> ShowS)
 -> (scmp -> ShowS)
 -> (stmt -> ShowS)
 -> (ext -> ShowS)
 -> (cmp -> ShowS)
 -> (a -> ShowS)
 -> Patt lcmp lhs scmp stmt ext cmp a -> ShowS
showPatt slc sl ssc ss sx sc sa (Patt eb) =
  showExtendBlock
    (showPun slc sl (showPatt slc sl ssc ss sx sc sa) ssc ss)
    sx
    (showPath sc sa)
    eb

fromPatt
 :: Patt_ p
 => (lcmp -> Compound (Lhs (Stmt p)))
 -> (lhs -> Lhs (Stmt p))
 -> (scmp -> Compound (Stmt p))
 -> (stmt -> Stmt p)
 -> (ext -> Ext p)
 -> (cmp -> Compound p)
 -> (a -> p)
 -> Patt lcmp lhs scmp stmt ext cmp a -> p
fromPatt slc sl ssc ss sx sc sa (Patt eb) =
  fromExtendBlock
    (fromPun
      slc
      sl
      (fromPatt slc sl ssc ss sx sc sa)
      ssc
      ss)
    sx
    (fromPath sc sa)
    eb
  
-- | Let pattern statement (define a pattern to be equal to a value)
type LetPatt plcmp plhs pscmp pstmt pext pcmp lhs =
  Let (Patt plcmp plhs pscmp pstmt pext pcmp lhs)

type LetPatt_ s = (Let s, Patt (Lhs s))
-- s, Lhs s, Rhs s, Compound (Lhs s), ...

showLetPatt
 :: (plcmp -> ShowS)
 -> (plhs -> ShowS)
 -> (pscmp -> ShowS)
 -> (pstmt -> ShowS)
 -> (pext -> ShowS)
 -> (pcmp -> ShowS)
 -> (lhs -> ShowS)
 -> (rhs -> ShowS)
 -> (a -> ShowS)
 -> LetPatt plcmp plhs pscmp pstmt pext pcmp lhs rhs a -> ShowS
showLetPatt splc spl spsc sps spx spc sl sr sa =
  showLet (showPatt splc spl spsc sps spx spc sl) sr sa
  
{-
-- | Parse a statement of a block expression
parsePun
 :: ( Let s
    , IsString_ (Lhs s), Path_ (Lhs s)
    , IsString s, Path_ s
    ) => Parser (Path Void Void -> Rhs s) -> Parser s
parsePun p =
  do
    p <- localpath <|> relpath
    (do
      eq <- parseLet
      rhs <- p
      return (fromPath absurd absurd p `eq` rhs))
      <|> return (fromPath absurd absurd p)
  where
    identFirst :: forall x . (IsString_ x, Path_ x) => x
    identFirst = do
      Ident s <- parseIdent
      (do
        f <- parseChain1
        return (f (fromString s)))
        
      <|> return (fromString s)
        (do
          eq <- parseLet
          rhs <- p
          return (f (fromString s) `eq` rhs))
        <|> return (f (fromString s)))
        
    letNext
      :: Compound (Lhs r) -> (Compound (Lhs r) -> Lhs r) -> r
    letNext s f =
      (do
        
      
  f <- relpath <|> localpath
  pubfirst          -- '.' alpha ...
    <|> pattfirst   -- alpha ...
                    -- '(' ...
    <|> escfirst    -- '^' ...
    <?> "statement"
  where
    pubfirst = do
      ARelPath apath <- relpath
      ((`id` apath) <$> pattrest <**> assign <*> p  -- '{' ...
                                                    -- '=' ...
        <|> return apath)
      
    pattfirst =
      (localpath      -- alpha ...
        <|> pattblock)  -- '{' ...
        <**> pattrest <**> assign <*> p
      
    pattrest :: Patt p => Parser (p -> p)
    pattrest = iter (liftA2 flip extend pattblock)
          
    pattblock
      :: (Block p, Pun (Stmt p), LetMatch (Stmt p), Patt (Lower (Rhs (Stmt p))))
      => Parser p
    pattblock = block (match patt) 
    
    patt :: Patt p => Parser p 
    patt =
      (relpath          -- '.' alpha
        <|> localpath   -- alpha
        <|> pattblock)  -- '{'
        <**> pattrest
        <?> "pattern"
        
    escfirst = esc <*>
      (localpath         -- '.' alpha ..
        <|> relpath)     -- alpha ...
-}

fromLetPatt
 :: LetPatt_ s
 => (plcmp -> Compound (Lhs (Stmt (Lhs s))))
 -> (plhs -> Lhs (Stmt (Lhs s)))
 -> (pscmp -> Compound (Stmt (Lhs s)))
 -> (pstmt -> Stmt (Lhs s))
 -> (pext -> Ext (Lhs s))
 -> (pcmp -> Compound (Lhs s))
 -> (lhs -> Lhs s)
 -> (rhs -> Rhs s)
 -> (a -> s)
fromLetPatt kplc kpl kpsc kps kpx kpc kl kr ka =
  fromLet (fromPatt kplc kpl kpsc kps kpx kpc kl) kr ka
