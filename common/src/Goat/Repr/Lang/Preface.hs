module Goat.Repr.Lang.Preface


newtype Include k f =
  Include { getInclude :: ResMod k (ResInc k f (Mod f)) }
  
includePlainModule :: Module k f -> Include k f
includePlainModule (Module ks res) =
  Include (plainMod res <&> (\ f -> f [] [] <&> Mod ks))
  
instance (Ord k, S.IsString k, Applicative f, Foldable f)
 => S.Module_ (Include k (Dyn k f)) where
  type ModuleStmt (Include k (Dyn k f)) =
    Stmt [P.Vis (Path k) (Path k)]
      ( Patt (Matches k) Bind
      , Synt (Res k) (Eval (Dyn k f))
      )
  module_ rs = includePlainModule (S.module_ rs)

instance (Applicative f, Foldable f, S.IsString k, Ord k)
 => S.Include_ (Include k (Dyn k f)) where
  type Inc (Include k (Dyn k f)) = Module k (Dyn k f)
  include_ n (Module ks res) = Include
    (asks (handleUse n)
      >>= maybe
        (tell [e] >> return (moduleError e))
        (return . reader)
      >>= includeMod res
      >>= return . fmap (Mod ks) )
    where
      e = ScopeError (NotModule n)


      
data Module k f = Module [P.Ident] (Res k (Eval f))

instance (S.IsString k, Ord k, Foldable f, Applicative f)
 => S.Module_ (Module k (Dyn k f)) where
  type ModuleStmt (Module k (Dyn k f)) =
    Stmt [P.Vis (Path k) (Path k)]
      ( Patt (Matches k) Bind
      , Synt (Res k) (Eval (Dyn k f))
      )
  module_ rs = Module ks (readSynt (S.block_ rs))
    where
      ks = nub
        (foldMap (\ (Stmt (ps, _)) -> mapMaybe pubname ps) rs)
        
      pubname :: P.Vis (Path k) (Path k) -> Maybe P.Ident
      pubname (P.Pub (Path n _)) = Just n
      pubname (P.Priv _)         = Nothing

      
data Import k f =
  Import
    [FilePath]
    (ReaderT 
      [ResMod k (ResInc k f (Mod f))]
      (ResMod k)
      (ResInc k f (Mod f)))
    
importPlainInclude :: Include k f -> Import k f
importPlainInclude (Include resmod) =
  Import [] (lift resmod)

importPlainModule :: Module k f -> Import k f
importPlainModule = importPlainInclude . includePlainModule

instance (Applicative f, Foldable f, S.IsString k, Ord k)
 => S.Module_ (Import k (Dyn k f)) where
  type ModuleStmt (Import k (Dyn k f)) =
    Stmt [P.Vis (Path k) (Path k)]
      ( Patt (Matches k) Bind
      , Synt (Res k) (Eval (Dyn k f))
      )
  module_ rs = importPlainModule (S.module_ rs)

instance (Applicative f, Foldable f, S.IsString k, Ord k)
 => S.Include_ (Import k (Dyn k f)) where
  type Inc (Import k (Dyn k f)) = Module k (Dyn k f)
  include_ n inc = importPlainInclude (S.include_ n inc)
  
newtype ImportPath = ImportPath FilePath

instance S.Text_ ImportPath where
  quote_ = ImportPath
        
instance (Applicative f)
 => S.Imports_ (Import k (Dyn k f)) where
  type ImportStmt (Import k (Dyn k f)) =
    Stmt [P.Ident] (Plain Bind, ImportPath)
  type Imp (Import k (Dyn k f)) = Include k (Dyn k f)
  extern_ rs (Include resmod) = Import 
    fps'
    (ReaderT (\ mods ->
      (dynCheckImports kv'
        >>= \ kv ->
          applyImports
            ns
            (map (resolveMods mods kv Map.!) ns)
            resmod)))
    where
      resolveMods mods =
        Map.map
          (either
            (return . moduleError)
            (mods!!))
      
      (Comps kv, fps) = buildImports rs
        :: ( Comps P.Ident [Maybe Int]
           , [(Plain Bind, ImportPath)]
           )
      
      kv' = Comps kv
      
      fps' = foldMap (\ (p, ImportPath fp) -> matchPlain p fp) fps
      
      ns = nub
        (foldMap (\ (Stmt (ns, _)) -> ns) rs)



importProof
 :: (Applicative f, Foldable f, S.IsString k, Ord k)
 => SomePreface SomeLetImport SomeDefn -> Import k (Dyn k f)
importProof =
  run . fromPreface (run . fromLetImport) (run . fromDefn)
  