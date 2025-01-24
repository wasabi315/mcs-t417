module T417.Verifier where

import Data.Coerce
import Data.Function
import Data.Vector (Vector)
import Data.Vector qualified as V
import Prettyprinter
import T417.Common
import T417.Rule
import T417.Syntax

--------------------------------------------------------------------------------

-- Δ; Γ ⊢ M : N
data Judgment = Judgment
  { defs :: [(ConstName, Def)],
    ctx :: [(VarName, Type)],
    term :: Term,
    type_ :: Type
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

verify :: Rules -> Vector Judgment
verify (Rules rs) = fix \ ~jdgs -> flip V.map rs \case
  RSort -> verifySort
  RVar (RuleIx i) x -> verifyVar (jdgs V.! i) x
  RWeak (RuleIx i) (RuleIx j) x -> verifyWeak (jdgs V.! i) (jdgs V.! j) x
  RForm (RuleIx i) (RuleIx j) -> verifyForm (jdgs V.! i) (jdgs V.! j)
  RAppl (RuleIx i) (RuleIx j) -> verifyAppl (jdgs V.! i) (jdgs V.! j)
  RAbst (RuleIx i) (RuleIx j) -> verifyAbst (jdgs V.! i) (jdgs V.! j)
  RConv (RuleIx i) (RuleIx j) -> verifyConv (jdgs V.! i) (jdgs V.! j)
  RDef (RuleIx i) (RuleIx j) c -> verifyDef (jdgs V.! i) (jdgs V.! j) c
  RDefpr (RuleIx i) (RuleIx j) c -> verifyDefpr (jdgs V.! i) (jdgs V.! j) c
  RInst (RuleIx i) js p -> verifyInst (jdgs V.! i) ((jdgs V.!) . coerce <$> js) p
  RCp (RuleIx i) -> jdgs V.! i
  RSp (RuleIx i) j -> verifySp (jdgs V.! i) j

expectSort :: Type -> ()
expectSort = \case
  Type -> ()
  Kind -> ()
  _ -> error "expected sort"

expectFresh :: [(VarName, Type)] -> VarName -> ()
expectFresh ctx x = case lookup x ctx of
  Nothing -> ()
  Just _ -> error "expected fresh"

expectFreshConst :: [(ConstName, Def)] -> ConstName -> ()
expectFreshConst defs c = case lookup c defs of
  Nothing -> ()
  Just _ -> error "expected fresh"

expectAlphaEq :: Term -> Term -> ()
expectAlphaEq t u
  | alphaEq [] [] t u = ()
  | otherwise = error "expected alpha-equivalent"

expectAlphaEqCtx :: [(VarName, Type)] -> [(VarName, Type)] -> ()
expectAlphaEqCtx ctx1 ctx2
  | and (zipWith (\(x, a) (y, b) -> x == y && alphaEq [] [] a b) ctx1 ctx2) = ()
  | otherwise = error "expected alpha-equivalent contexts"

expectBetaDeltaEq :: [(ConstName, Def)] -> Term -> Term -> ()
expectBetaDeltaEq defs t u
  | alphaEq [] [] t' u' = ()
  | otherwise =
      error $ "expected beta-delta-equivalent: " ++ show (pretty t') ++ " and " ++ show (pretty u')
  where
    t' = nf defs t
    u' = nf defs u

expectPi :: Type -> (VarName, Type, Type)
expectPi = \case
  Pi x a b -> (x, a, b)
  _ -> error "expected Pi"

expectSameVar :: VarName -> VarName -> ()
expectSameVar x y
  | x == y = ()
  | otherwise = error "expected same variable"

verifySort :: Judgment
verifySort =
  Judgment
    { defs = [],
      ctx = [],
      term = Type,
      type_ = Kind
    }

verifyVar :: Judgment -> VarName -> Judgment
verifyVar jdg v =
  let _ = expectSort jdg.type_
      _ = expectFresh jdg.ctx v
      ctx = (v, jdg.term) : jdg.ctx
      term = Var v
      type_ = jdg.term
   in jdg {ctx, term, type_}

verifyWeak :: Judgment -> Judgment -> VarName -> Judgment
verifyWeak jdg1 jdg2 v =
  let _ = expectSort jdg2.type_
      _ = expectAlphaEqCtx jdg1.ctx jdg2.ctx
      _ = expectFresh jdg1.ctx v
      ctx = (v, jdg2.term) : jdg1.ctx
   in jdg1 {ctx}

verifyForm :: Judgment -> Judgment -> Judgment
verifyForm jdg1 jdg2 =
  let _ = expectSort jdg1.type_
      _ = expectSort jdg2.type_
      _ = expectAlphaEqCtx jdg1.ctx (tail jdg2.ctx)
      (x, a) = head jdg2.ctx
      _ = expectAlphaEq a jdg1.term
      term = Pi x a jdg2.term
      type_ = jdg2.type_
   in jdg1 {term, type_}

verifyAppl :: Judgment -> Judgment -> Judgment
verifyAppl jdg1 jdg2 =
  let (x, a, b) = expectPi jdg1.type_
      _ = expectAlphaEq a jdg2.type_
      _ = expectAlphaEqCtx jdg1.ctx jdg2.ctx
      term = App jdg1.term jdg2.term
      type_ = subst x jdg2.term b
   in jdg1 {term, type_}

verifyAbst :: Judgment -> Judgment -> Judgment
verifyAbst jdg1 jdg2 =
  let _ = expectSort jdg2.type_
      ((x, a) : ctx) = jdg1.ctx
      (x', a', b') = expectPi jdg2.term
      _ = expectSameVar x x'
      _ = expectAlphaEq a a'
      _ = expectAlphaEq jdg1.type_ b'
      _ = expectAlphaEqCtx ctx jdg2.ctx
      term = Lam x a jdg1.term
      type_ = jdg2.term
   in jdg2 {term, type_}

verifyConv :: Judgment -> Judgment -> Judgment
verifyConv jdg1 jdg2 =
  let _ = expectSort jdg2.type_
      _ = expectAlphaEqCtx jdg1.ctx jdg2.ctx
      _ = expectBetaDeltaEq jdg1.defs jdg1.type_ jdg2.term
   in jdg1 {type_ = jdg2.term}

verifyDef :: Judgment -> Judgment -> ConstName -> Judgment
verifyDef jdg1 jdg2 c =
  let _ = expectFreshConst jdg1.defs c
      params = reverse jdg2.ctx
      retTy = jdg2.type_
      body = Just jdg2.term
      def = Def {name = c, params, retTy, body}
      defs = (c, def) : jdg1.defs
   in jdg1 {defs}

verifyDefpr :: Judgment -> Judgment -> ConstName -> Judgment
verifyDefpr jdg1 jdg2 c =
  let _ = expectFreshConst jdg1.defs c
      params = reverse jdg2.ctx
      retTy = jdg2.type_
      def = Def {name = c, params, retTy, body = Nothing}
      defs = jdg1.defs ++ [(c, def)]
   in jdg1 {defs}

verifyInst :: Judgment -> [Judgment] -> Int -> Judgment
verifyInst jdg jdgs p =
  let _ = expectSort jdg.term
      _ = expectSort jdg.type_
      (_, def) = jdg.defs !! (length jdg.defs - p - 1)
      term = Const def.name $ map (\jdg' -> jdg'.term) jdgs
      s = zipWith (\(x, _) jdg' -> (x, jdg'.term)) def.params jdgs
      type_ = substMany s def.retTy
   in jdg {term, type_}

verifySp :: Judgment -> Int -> Judgment
verifySp jdg i =
  let (x, type_) = jdg.ctx !! (length jdg.ctx - i - 1)
      term = Var x
   in jdg {term, type_}
