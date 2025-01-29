module T417.Verifier where

import Control.Applicative ((<|>))
import Control.Exception
import Control.Monad
import Data.Foldable
import Data.HashMap.Strict qualified as HM
import Data.Maybe
import Prettyprinter
import Prettyprinter.Util
import T417.AlphaConv
import T417.Common
import T417.Rule
import T417.Syntax

--------------------------------------------------------------------------------

newtype Error = Error String

instance Show Error where
  show (Error s) = s

instance Exception Error where
  displayException (Error s) = s

throwError :: String -> IO a
throwError = throwIO . Error

--------------------------------------------------------------------------------

-- Δ; Γ ⊢ M : N
data Judgment = Judgment
  { defs :: [(ConstName, Def)],
    ctx :: [(VarName, AType)],
    term :: Term,
    type_ :: AType
  }
  deriving stock (Show)

instance Pretty Judgment where
  pretty Judgment {..} =
    ";"
      <+> hsep (reverse $ map (\(x, a) -> pretty x <> ":" <> pretty a) ctx)
      <+> "⊢"
      <+> pretty term
      <+> ":"
      <+> pretty type_

--------------------------------------------------------------------------------

expectSort :: Type -> IO ()
expectSort = \case
  Type -> pure ()
  Kind -> pure ()
  _ -> throwError "expected sort"

expectASort :: AType -> IO ()
expectASort = \case
  AType -> pure ()
  AKind -> pure ()
  _ -> throwError "expected sort"

expectFresh :: [(VarName, a)] -> VarName -> IO ()
expectFresh ctx x = case lookup x ctx of
  Nothing -> pure ()
  Just _ -> throwError "expected fresh"

expectFreshConst :: [(ConstName, Def)] -> ConstName -> IO ()
expectFreshConst defs c = case lookup c defs of
  Nothing -> pure ()
  Just _ -> throwError "expected fresh"

expectAlphaEq :: ATerm -> ATerm -> IO ()
expectAlphaEq t u
  | alphaConv t u = pure ()
  | otherwise = throwError "expected alpha-equivalent"

expectAlphaEqCtx :: [(VarName, AType)] -> [(VarName, AType)] -> IO ()
expectAlphaEqCtx ctx1 ctx2
  | and (zipWith (\(x, a) (y, b) -> x == y && alphaConv a b) ctx1 ctx2) = pure ()
  | otherwise = throwError "expected alpha-equivalent contexts"

expectBetaDeltaEq :: [(ConstName, Def)] -> Term -> Term -> IO ()
expectBetaDeltaEq defs t u
  | nalphaEq Rigid [] [] t' u' = pure ()
  | otherwise =
      throwError $ "expected beta-delta-equivalent:\n" ++ show (pretty $ fromNf t') ++ " and\n" ++ show (pretty $ fromNf u')
  where
    t' = nf defs t
    u' = nf defs u

expectAPi :: AType -> IO (AType, AClosure)
expectAPi = \case
  APi a b -> pure (a, b)
  _ -> throwError "expected Pi"

expectSameVar :: VarName -> VarName -> IO ()
expectSameVar x y
  | x == y = pure ()
  | otherwise = throwError "expected same variable"

expectNonEmpty :: [a] -> IO (a, [a])
expectNonEmpty [] = throwError "expected non-empty list"
expectNonEmpty (x : xs) = pure (x, xs)

--------------------------------------------------------------------------------

verify :: Rules -> IO ()
verify (Rules rs) = void $ foldlM f (HM.empty, HM.empty, 0) rs
  where
    f (!tjdgs, !ljdgs, !n) rule = do
      let lookupJdg (RuleIx i) = fromJust $ HM.lookup i ljdgs <|> HM.lookup i tjdgs
      jdg <- case rule of
        RSort -> pure verifySort
        RVar i x -> verifyVar (lookupJdg i) x
        RWeak i j x -> verifyWeak (lookupJdg i) (lookupJdg j) x
        RForm i j -> verifyForm (lookupJdg i) (lookupJdg j)
        RAppl i j -> verifyAppl (lookupJdg i) (lookupJdg j)
        RAbst i j -> verifyAbst (lookupJdg i) (lookupJdg j)
        RConv i j -> verifyConv (lookupJdg i) (lookupJdg j)
        RDef i j c -> verifyDef (lookupJdg i) (lookupJdg j) c
        RDefpr i j c -> verifyDefpr (lookupJdg i) (lookupJdg j) c
        RInst i js p -> verifyInst (lookupJdg i) (map lookupJdg js) p
        RCp i -> pure $! lookupJdg i
        RSp i j -> verifySp (lookupJdg i) j
      putDocW 80 $ pretty n <+> ":" <+> pretty jdg <> line
      pure case rule of
        RDef {} -> (HM.insert n jdg tjdgs, HM.empty, n + 1)
        RDefpr {} -> (HM.insert n jdg tjdgs, HM.empty, n + 1)
        _ -> (tjdgs, HM.insert n jdg ljdgs, n + 1)

verifySort :: Judgment
verifySort =
  Judgment
    { defs = [],
      ctx = [],
      term = Type,
      type_ = AKind
    }

verifyVar :: Judgment -> VarName -> IO Judgment
verifyVar jdg v = do
  expectASort jdg.type_
  expectFresh jdg.ctx v
  let type_ = toATerm [] jdg.term
      ctx = (v, type_) : jdg.ctx
      term = Var v
  pure $! jdg {ctx, term, type_}

verifyWeak :: Judgment -> Judgment -> VarName -> IO Judgment
verifyWeak jdg1 jdg2 v = do
  expectASort jdg2.type_
  expectAlphaEqCtx jdg1.ctx jdg2.ctx
  expectFresh jdg1.ctx v
  let c = toATerm [] jdg2.term
      ctx = (v, c) : jdg1.ctx
  pure $! jdg1 {ctx}

verifyForm :: Judgment -> Judgment -> IO Judgment
verifyForm jdg1 jdg2 = do
  expectASort jdg1.type_
  expectASort jdg2.type_
  expectAlphaEqCtx jdg1.ctx (tail jdg2.ctx)
  let (x, a) = head jdg2.ctx
      a' = toATerm [] jdg1.term
  expectAlphaEq a a'
  let term = Pi x (fromATerm a) jdg2.term
      type_ = jdg2.type_
  pure $! jdg1 {term, type_}

verifyAppl :: Judgment -> Judgment -> IO Judgment
verifyAppl jdg1 jdg2 = do
  (a, b) <- expectAPi jdg1.type_
  expectAlphaEq a jdg2.type_
  expectAlphaEqCtx jdg1.ctx jdg2.ctx
  let term = App jdg1.term jdg2.term
      n = toATerm [] jdg2.term
      type_ = b $$ n
  pure $! jdg1 {term, type_}

verifyAbst :: Judgment -> Judgment -> IO Judgment
verifyAbst jdg1 jdg2 = do
  expectASort jdg2.type_
  ((x, a), ctx) <- expectNonEmpty jdg1.ctx
  let type_ = toATerm [] jdg2.term
  (a', b'@(AClosure x' _ _)) <- expectAPi type_
  expectSameVar x x'
  expectAlphaEq a a'
  expectAlphaEq jdg1.type_ (b' $$ AVar x)
  expectAlphaEqCtx ctx jdg2.ctx
  let term = Lam x (fromATerm a) jdg1.term
  pure $! jdg2 {term, type_}

verifyConv :: Judgment -> Judgment -> IO Judgment
verifyConv jdg1 jdg2 = do
  expectASort jdg2.type_
  expectAlphaEqCtx jdg1.ctx jdg2.ctx
  expectBetaDeltaEq jdg1.defs (fromATerm jdg1.type_) jdg2.term
  let type_ = toATerm [] jdg2.term
  pure $! jdg1 {type_}

verifyDef :: Judgment -> Judgment -> ConstName -> IO Judgment
verifyDef jdg1 jdg2 c = do
  expectFreshConst jdg1.defs c
  let params = reverse $ map (\(x, a) -> (x, fromATerm a)) jdg2.ctx
      retTy = fromATerm jdg2.type_
      body = Just jdg2.term
      def = Def {name = c, params, retTy, body}
      defs = (c, def) : jdg1.defs
  pure $! jdg1 {defs}

verifyDefpr :: Judgment -> Judgment -> ConstName -> IO Judgment
verifyDefpr jdg1 jdg2 c = do
  expectFreshConst jdg1.defs c
  expectASort jdg2.type_
  let params = reverse $ map (\(x, a) -> (x, fromATerm a)) jdg2.ctx
      retTy = jdg2.term
      def = Def {name = c, params, retTy, body = Nothing}
      defs = (c, def) : jdg1.defs
  pure $! jdg1 {defs}

verifyInst :: Judgment -> [Judgment] -> Int -> IO Judgment
verifyInst jdg jdgs p = do
  expectSort jdg.term
  expectASort jdg.type_
  let (_, def) = jdg.defs !! (length jdg.defs - p - 1)
      sub = zipWith (\(x, _) jdg' -> (x, jdg'.term)) def.params jdgs
      -- Check that the types of the arguments match the expected types
      _ =
        flip assert () $
          and $
            zipWith (\(_, a) jdg' -> alphaConv (toATerm [] $ substMany sub a) jdg'.type_) def.params jdgs
      term = Const def.name $ map (\jdg' -> jdg'.term) jdgs
      type_ = toATerm [] $ substMany sub def.retTy
  pure $! jdg {term, type_}

verifySp :: Judgment -> Int -> IO Judgment
verifySp jdg i = do
  let (x, type_) = jdg.ctx !! (length jdg.ctx - i - 1)
      term = Var x
  pure $! jdg {term, type_}
