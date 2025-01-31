module T417.Verifier where

import Control.Applicative ((<|>))
import Control.Exception
import Control.Monad
import Data.Foldable
import Data.Functor
import Data.HashMap.Strict qualified as HM
import Data.Maybe
import Data.Traversable
import Prettyprinter
import StrictList qualified as SL
import T417.AlphaConv
import T417.Common
import T417.Evaluation
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
  { topCtxLen :: Int,
    topCtx :: [(ConstName, ATopClosure, TopClosure)],
    ctxLen :: Int,
    ctx :: [(VarName, AType, VType)],
    term :: Term,
    tenv :: TopEnv,
    lenv :: LocalEnv,
    type_ :: AType,
    vtype :: ~VType
  }

instance Pretty Judgment where
  pretty Judgment {..} =
    ";"
      <+> hsep (punctuate comma $ reverse $ map (\(x, a, _) -> pretty x <> ":" <> pretty a) ctx)
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

expectFresh :: [(VarName, a, b)] -> VarName -> IO ()
expectFresh = \cases
  [] _ -> pure ()
  ((v, _, _) : ctx) v'
    | v == v' -> throwError "expected fresh"
    | otherwise -> expectFresh ctx v'

expectFreshConst :: [(ConstName, a, b)] -> ConstName -> IO ()
expectFreshConst = \cases
  [] _ -> pure ()
  ((c, _, _) : defs) c'
    | c == c' -> throwError "expected fresh"
    | otherwise -> expectFreshConst defs c

expectAlphaConv :: ATerm -> ATerm -> IO ()
expectAlphaConv t u
  | alphaConv t u = pure ()
  | otherwise = throwError "expected alpha-equivalent"

expectAlphaConvCtx :: [(VarName, AType, a)] -> [(VarName, AType, a)] -> IO ()
expectAlphaConvCtx = zipWithM_ (\(x, a, _) (y, b, _) -> expectSameVar x y *> expectAlphaConv a b)

expectBetaDeltaConv :: Value -> Value -> IO ()
expectBetaDeltaConv v1 v2
  | bdConv Rigid v1 v2 = pure ()
  | otherwise = throwError "expected βδ-convertible"

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
        RInst i js p -> verifyInst (lookupJdg i) (lookupJdg <$> js) p
        RCp i -> pure $! lookupJdg i
        RSp i j -> verifySp (lookupJdg i) j
      -- print $ pretty n <+> ":" <+> pretty jdg
      pure
        if isDefRule rule
          then (HM.insert n jdg tjdgs, ljdgs, n + 1)
          else (tjdgs, HM.insert n jdg ljdgs, n + 1)

verifySort :: Judgment
verifySort =
  Judgment
    { topCtxLen = 0,
      topCtx = [],
      ctxLen = 0,
      ctx = [],
      term = Type,
      type_ = AKind,
      tenv = [],
      lenv = [],
      vtype = VKind
    }

verifyVar :: Judgment -> VarName -> IO Judgment
verifyVar jdg v = do
  expectASort jdg.type_
  expectFresh jdg.ctx v
  let type_ = toATerm [] jdg.term
      ~vtype = eval jdg.tenv jdg.lenv jdg.term
      ctxLen = jdg.ctxLen + 1
      ctx = (v, type_, vtype) : jdg.ctx
      lenv = (v, VVar v SNil) : jdg.lenv
      term = Var v
  pure $! jdg {ctxLen, ctx, term, type_, lenv, vtype}

verifyWeak :: Judgment -> Judgment -> VarName -> IO Judgment
verifyWeak jdg1 jdg2 v = do
  expectASort jdg2.type_
  expectAlphaConvCtx jdg1.ctx jdg2.ctx
  expectFresh jdg1.ctx v
  let c = toATerm [] jdg2.term
      ~vc = eval jdg2.tenv jdg2.lenv jdg2.term
      ctxLen = jdg1.ctxLen + 1
      ctx = (v, c, vc) : jdg1.ctx
      lenv = (v, VVar v SNil) : jdg1.lenv
  pure $! jdg1 {ctxLen, ctx, lenv}

verifyForm :: Judgment -> Judgment -> IO Judgment
verifyForm jdg1 jdg2 = do
  expectASort jdg1.type_
  expectASort jdg2.type_
  expectAlphaConvCtx jdg1.ctx (tail jdg2.ctx)
  let (x, a, _) = head jdg2.ctx
      a' = toATerm [] jdg1.term
  expectAlphaConv a a'
  let term = Pi x (fromATerm a) jdg2.term
      type_ = jdg2.type_
      ~vtype = jdg2.vtype
  pure $! jdg1 {term, type_, vtype}

verifyAppl :: Judgment -> Judgment -> IO Judgment
verifyAppl jdg1 jdg2 = do
  (a, b) <- expectAPi jdg1.type_
  expectAlphaConv a jdg2.type_
  expectAlphaConvCtx jdg1.ctx jdg2.ctx
  let term = App jdg1.term jdg2.term
      n = toATerm [] jdg2.term
      type_ = b $$ n
      VPi _ vb = jdg1.vtype
      ~vtype = Lazy vb $$ eval jdg2.tenv jdg2.lenv jdg2.term
  pure $! jdg1 {term, type_, vtype}

verifyAbst :: Judgment -> Judgment -> IO Judgment
verifyAbst jdg1 jdg2 = do
  expectASort jdg2.type_
  ((x, a, _), ctx) <- expectNonEmpty jdg1.ctx
  let type_ = toATerm [] jdg2.term
      ~vtype = eval jdg2.tenv jdg2.lenv jdg2.term
  (a', b'@(AClosure x' _ _)) <- expectAPi type_
  expectSameVar x x'
  expectAlphaConv a a'
  expectAlphaConv jdg1.type_ (b' $$ AVar x)
  expectAlphaConvCtx ctx jdg2.ctx
  let term = Lam x (fromATerm a) jdg1.term
  pure $! jdg2 {term, type_, vtype}

verifyConv :: Judgment -> Judgment -> IO Judgment
verifyConv jdg1 jdg2 = do
  expectASort jdg2.type_
  expectAlphaConvCtx jdg1.ctx jdg2.ctx
  let vtype = eval jdg2.tenv jdg2.lenv jdg2.term
  expectBetaDeltaConv jdg1.vtype vtype
  let type_ = toATerm [] jdg2.term
  pure $! jdg1 {type_, vtype}

verifyDef :: Judgment -> Judgment -> ConstName -> IO Judgment
verifyDef jdg1 jdg2 c = do
  expectFreshConst jdg1.topCtx c
  let retTy = fromATerm jdg2.type_
      acl = ATopClosure jdg2.ctx retTy
      cl = TopClosure jdg2.ctx jdg2.tenv retTy
      topCtxLen = jdg2.topCtxLen + 1
      topCtx = (c, acl, cl) : jdg2.topCtx
      tenv = (c, TopClosure jdg2.ctx jdg2.tenv jdg2.term) : jdg2.tenv
  pure $! jdg1 {tenv, topCtxLen, topCtx}

verifyDefpr :: Judgment -> Judgment -> ConstName -> IO Judgment
verifyDefpr jdg1 jdg2 c = do
  expectFreshConst jdg1.topCtx c
  expectASort jdg2.type_
  let retTy = jdg2.term
      acl = ATopClosure jdg2.ctx retTy
      cl = TopClosure jdg2.ctx jdg2.tenv retTy
      topCtxLen = jdg2.topCtxLen + 1
      topCtx = (c, acl, cl) : jdg2.topCtx
  pure $! jdg1 {topCtxLen, topCtx}

verifyInst :: Judgment -> SL.List Judgment -> Int -> IO Judgment
verifyInst jdg jdgs p = do
  expectSort jdg.term
  expectASort jdg.type_
  let (name, ty, vty) = jdg.topCtx !! (jdg.topCtxLen - p - 1)
  (_, args) <- case ty of
    ATopClosure ctx _ -> do
      mapAccumM
        ( \env (jdg', (x, a, _)) -> do
            let a' = toATerm env (fromATerm a)
                t = toATerm [] jdg'.term
                e' = (x, t) : env
            expectAlphaConv a' jdg'.type_
            pure (e', t)
        )
        []
        (zip (toList jdgs) (reverse ctx))
  let term = Const name $ jdgs <&> \jdg' -> jdg'.term
      type_ = ty $$ args
      vargs = reverse $ map (\jdg' -> eval jdg'.tenv jdg'.lenv jdg'.term) $ SL.toListReversed jdgs
      ~vtype = Lazy vty $$ vargs
  pure $! jdg {term, type_, vtype}

verifySp :: Judgment -> Int -> IO Judgment
verifySp jdg i = do
  let (x, type_, vtype) = jdg.ctx !! (jdg.ctxLen - i - 1)
      term = Var x
  pure $! jdg {term, type_, vtype}
