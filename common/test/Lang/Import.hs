{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts, OverloadedLists #-}

module Lang.Import (tests) where

import Goat.Lang.Class
import Goat.Lang.Parser
  (CanonPreface, showPreface, toPreface)
import Goat.Lang.Error
  ( ImportError
  , displayImportError, displayErrorList
  )
import Test.HUnit
import Control.Exception (bracket)
import Data.Foldable (traverse_)
import System.FilePath ((</>), dropDrive)
import System.IO (writeFile)
import System.Directory
  (removeFile, createDirectory, removeDirectory)

banner :: CanonPreface -> String
banner r = "For " ++ showPreface (toPreface r) ","


parses :: Either [ImportError] a -> IO a
parses = either 
  (fail . displayErrorList displayImportError)
  return

withFiles
 :: FilePath
 -> [(String, CanonPreface)]
 -> IO a
 -> IO a
withFiles dir ps io
  = bracket acq rel (\_ -> io)
  where
  acq
    = do
      createDirectory dir
      traverse
        (\ (fp, pfc)
         -> let
            abspath = dir </> dropDrive fp
            content = showPreface (toPreface pfc) ""
            in 
            do 
              writeFile abspath content
              return abspath)
        ps
  rel abspaths
    = do
      traverse_ removeFile abspaths
      removeDirectory dir

tests
 :: (Preface_ a, Definition_ b, Eq c, Show c)
 => FilePath
 -> (FilePath -> a -> IO (Either [ImportError] b))
 -> (b -> c)
 -> Test
tests dir load expr
  = TestList
  [ "parse a module with no imports"
     ~: let
        r :: Preface_ a => a
        r = module_ [
          "" #. "run" #= quote_ "module"
          ]
        e = "module"
        in
        do 
          a <- load dir r >>= parses
          assertEqual (banner r) (expr e) (expr a)

  , "import resolves to local .my file with same name"
     ~: let
        fs 
          = [ ( "ext.goat"
              , module_ [ "" #. "test" #=
                  quote_ "imported"
                  ]
              )
            ]
        r :: Preface_ a => a
        r = 
          extern_ [
            "import" #= quote_ "./ext.goat"
          ] $
          module_ [
            "" #. "run" #= use_ "import" #. "test"
          ]
        e = quote_ "imported"
        in do
          a
           <- withFiles dir fs
                (load dir r >>= parses)
          assertEqual (banner r) (expr e) (expr a)
  
  , "imported file resolves nested imports to directory with same name"
     ~: let
        r :: Preface_ a => a
        r = extern_ [
          "chain" #= quote_ "./chain.goat"
          ] $
          module_ [
            "" #. "run" #=
              use_ "chain" #. "test"
          ]
        fs
          = [ ( "./chain.goat"
              , extern_ [
                  "import" #=
                    quote_ "./chain/ext.goat"
                  ] $
                module_ [
                  "" #. "test" #=
                    use_ "import" #. "test"
                  ]
              )
            , ( "./chain/ext.goat"
              , module_ [
                  "" #. "test" #= "nested"
                  ]
              )
            ]
        e = "nested"
        in do
          a
           <- withFiles dir fs
                (load dir r >>= parses)
          assertEqual (banner r) (expr e) (expr a)
  
  ]
    
    