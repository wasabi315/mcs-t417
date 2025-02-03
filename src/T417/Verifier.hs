module T417.Verifier where

import Control.Applicative ((<|>))
import Control.Exception
import Control.Monad
import Data.Foldable
import Data.HashMap.Strict qualified as HM
import Data.Maybe
import Data.Monoid
import Mason.Builder
import Prettyprinter
import StrictList qualified as SL
import System.IO (stdout)
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

stringifyJudgment :: Judgment -> Builder
stringifyJudgment Judgment {..} =
  "; "
    <> ( case ctx of
           [] -> mempty
           (VarName x, a, _) : ctx' ->
             getDual
               ( foldMap
                   (\(VarName y, b, _) -> Dual $ textUtf8 y <> char8 ':' <> stringifyATerm b <> ", ")
                   ctx'
               )
               <> textUtf8 x
               <> char8 ':'
               <> stringifyATerm a
       )
    <> " ⊢ "
    <> stringifyTerm term
    <> " : "
    <> stringifyATerm type_

instance Pretty Judgment where
  pretty Judgment {..} =
    ";"
      <+> hsep (punctuate comma $ reverse $ map (\(x, a, _) -> pretty x <> ":" <> pretty a) ctx)
      <+> "⊢"
      <+> pretty term
      <+> ":"
      <+> pretty type_

--------------------------------------------------------------------------------

type M = Either String

expectSort :: Type -> M ()
expectSort = \case
  Type -> pure ()
  Kind -> pure ()
  _ -> Left "expected sort"

expectASort :: AType -> M ()
expectASort = \case
  AType -> pure ()
  AKind -> pure ()
  _ -> Left "expected sort"

expectFresh :: [(VarName, a, b)] -> VarName -> M ()
expectFresh = \cases
  [] _ -> pure ()
  ((v, _, _) : ctx) v'
    | v == v' -> Left "expected fresh"
    | otherwise -> expectFresh ctx v'

expectFreshConst :: [(ConstName, a, b)] -> ConstName -> M ()
expectFreshConst = \cases
  [] _ -> pure ()
  ((c, _, _) : defs) c'
    | c == c' -> Left "expected fresh"
    | otherwise -> expectFreshConst defs c

expectAlphaConv :: ATerm -> ATerm -> M ()
expectAlphaConv t u
  | alphaConv t u = pure ()
  | otherwise = Left "expected alpha-equivalent"

expectAlphaConvCtx :: [(VarName, AType, a)] -> [(VarName, AType, a)] -> M ()
expectAlphaConvCtx = zipWithM_ (\(x, a, _) (y, b, _) -> expectSameVar x y *> expectAlphaConv a b)

expectBetaDeltaConv :: Value -> Value -> M ()
expectBetaDeltaConv v1 v2
  | bdConv Rigid v1 v2 = pure ()
  | otherwise = Left "expected βδ-convertible"

expectAPi :: AType -> M (AType, AClosure)
expectAPi = \case
  APi a b -> pure (a, b)
  _ -> Left "expected Pi"

expectSameVar :: VarName -> VarName -> M ()
expectSameVar x y
  | x == y = pure ()
  | otherwise = Left "expected same variable"

expectNonEmpty :: [a] -> M (a, [a])
expectNonEmpty [] = Left "expected non-empty list"
expectNonEmpty (x : xs) = pure (x, xs)

--------------------------------------------------------------------------------

groupRules :: [RuleWithIx] -> [([RuleWithIx], Maybe RuleWithIx)]
groupRules = \case
  [] -> []
  rs -> let ~(rs', mr, rest) = go rs in (rs', mr) : groupRules rest
  where
    go = \case
      [] -> ([], Nothing, [])
      r@(_, RDef {}) : rs -> ([], Just r, rs)
      r@(_, RDefpr {}) : rs -> ([], Just r, rs)
      r : rs -> let ~(rs', mr, rest) = go rs in (r : rs', mr, rest)

verify :: Rules -> IO ()
verify = \(Rules rs) -> foldM_ f HM.empty $ groupRules rs
  where
    f tjdgs (rs, mr) = do
      ljdgs <- foldlM (g tjdgs) HM.empty rs
      let lookupJdg i = fromJust $ HM.lookup i ljdgs <|> HM.lookup i tjdgs
      case mr of
        Nothing -> pure tjdgs
        Just (n@(RuleIx n'), r) -> do
          jdg <- either throwError pure case r of
            RDef i j c -> verifyDef (lookupJdg i) (lookupJdg j) c
            RDefpr i j c -> verifyDefpr (lookupJdg i) (lookupJdg j) c
            _ -> error "impossible"
          hPutBuilder stdout $ intDec n' <> " : " <> stringifyJudgment jdg <> char8 '\n'
          pure $ HM.insert n jdg tjdgs

    g tjdgs ljdgs (n@(RuleIx n'), r) = do
      let lookupJdg i = fromJust $ HM.lookup i ljdgs <|> HM.lookup i tjdgs
      jdg <- either throwError pure case r of
        RSort -> pure verifySort
        RVar i x -> verifyVar (lookupJdg i) x
        RWeak i j x -> verifyWeak (lookupJdg i) (lookupJdg j) x
        RForm i j -> verifyForm (lookupJdg i) (lookupJdg j)
        RAppl i j -> verifyAppl (lookupJdg i) (lookupJdg j)
        RAbst i j -> verifyAbst (lookupJdg i) (lookupJdg j)
        RConv i j -> verifyConv (lookupJdg i) (lookupJdg j)
        RInst i js p -> verifyInst (lookupJdg i) (lookupJdg <$> js) p
        RCp i -> pure (lookupJdg i)
        RSp i j -> verifySp (lookupJdg i) j
        _ -> error "impossible"
      hPutBuilder stdout $ intDec n' <> " : " <> stringifyJudgment jdg <> char8 '\n'
      pure $ HM.insert n jdg ljdgs

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

verifyVar :: Judgment -> VarName -> M Judgment
verifyVar jdg v = do
  expectASort jdg.type_
  expectFresh jdg.ctx v
  let type_ = toATerm [] jdg.term
      ~vtype = eval jdg.tenv jdg.lenv jdg.term
      ctxLen = jdg.ctxLen + 1
      ctx = (v, type_, vtype) : jdg.ctx
      lenv = HM.insert v (VVar v SNil) jdg.lenv
      term = Var v
  pure jdg {ctxLen, ctx, term, type_, lenv, vtype}

verifyWeak :: Judgment -> Judgment -> VarName -> M Judgment
verifyWeak jdg1 jdg2 v = do
  expectASort jdg2.type_
  expectAlphaConvCtx jdg1.ctx jdg2.ctx
  expectFresh jdg1.ctx v
  let c = toATerm [] jdg2.term
      ~vc = eval jdg2.tenv jdg2.lenv jdg2.term
      ctxLen = jdg1.ctxLen + 1
      ctx = (v, c, vc) : jdg1.ctx
      lenv = HM.insert v (VVar v SNil) jdg1.lenv
  pure jdg1 {ctxLen, ctx, lenv}

verifyForm :: Judgment -> Judgment -> M Judgment
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
  pure jdg1 {term, type_, vtype}

verifyAppl :: Judgment -> Judgment -> M Judgment
verifyAppl jdg1 jdg2 = do
  (a, b) <- expectAPi jdg1.type_
  expectAlphaConv a jdg2.type_
  expectAlphaConvCtx jdg1.ctx jdg2.ctx
  let term = App jdg1.term jdg2.term
      n = toATerm [] jdg2.term
      type_ = b $$ n
      VPi _ vb = jdg1.vtype
      ~vtype = Lazy vb $$ eval jdg2.tenv jdg2.lenv jdg2.term
  pure jdg1 {term, type_, vtype}

verifyAbst :: Judgment -> Judgment -> M Judgment
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
  pure jdg2 {term, type_, vtype}

verifyConv :: Judgment -> Judgment -> M Judgment
verifyConv jdg1 jdg2 = do
  expectASort jdg2.type_
  expectAlphaConvCtx jdg1.ctx jdg2.ctx
  let vtype = eval jdg2.tenv jdg2.lenv jdg2.term
  expectBetaDeltaConv jdg1.vtype vtype
  let type_ = toATerm [] jdg2.term
  pure jdg1 {type_, vtype}

verifyDef :: Judgment -> Judgment -> ConstName -> M Judgment
verifyDef jdg1 jdg2 c = do
  expectFreshConst jdg1.topCtx c
  let retTy = fromATerm jdg2.type_
      ctx' = map (\(x, a, _) -> (x, a)) jdg2.ctx
      acl = ATopClosure ctx' retTy
      vars = map (\(x, _, _) -> x) jdg2.ctx
      cl = TopClosure vars jdg2.tenv retTy
      topCtxLen = jdg2.topCtxLen + 1
      topCtx = (c, acl, cl) : jdg2.topCtx
      tenv = HM.insert c (TopClosure vars jdg2.tenv jdg2.term) jdg2.tenv
  pure jdg1 {tenv, topCtxLen, topCtx}

verifyDefpr :: Judgment -> Judgment -> ConstName -> M Judgment
verifyDefpr jdg1 jdg2 c = do
  expectFreshConst jdg1.topCtx c
  expectASort jdg2.type_
  let retTy = jdg2.term
      ctx' = map (\(x, a, _) -> (x, a)) jdg2.ctx
      acl = ATopClosure ctx' retTy
      vars = map (\(x, _, _) -> x) jdg2.ctx
      cl = TopClosure vars jdg2.tenv retTy
      topCtxLen = jdg2.topCtxLen + 1
      topCtx = (c, acl, cl) : jdg2.topCtx
  pure jdg1 {topCtxLen, topCtx}

verifyInst :: Judgment -> [Judgment] -> Int -> M Judgment
verifyInst jdg jdgs p = do
  expectSort jdg.term
  expectASort jdg.type_
  let (name, ty@(ATopClosure (reverse -> ctxRev) _), vty) =
        jdg.topCtx !! (jdg.topCtxLen - p - 1)
      args = map (\jdg' -> toATerm [] jdg'.term) jdgs
      env = HM.fromList $ zipWith (\(x, _) arg -> (x, arg)) ctxRev args
  zipWithM_
    (\jdg' (_, a) -> expectAlphaConv (toATerm env (fromATerm a)) jdg'.type_)
    jdgs
    ctxRev
  let term = Const name $ SL.mapReversed (\jdg' -> jdg'.term) $ SL.fromListReversed jdgs
      type_ = ty $$ args
      vargs = map (\jdg' -> eval jdg'.tenv jdg'.lenv jdg'.term) jdgs
      ~vtype = Lazy vty $$ vargs
  pure jdg {term, type_, vtype}

verifySp :: Judgment -> Int -> M Judgment
verifySp jdg i = do
  let (x, type_, vtype) = jdg.ctx !! (jdg.ctxLen - i - 1)
      term = Var x
  pure jdg {term, type_, vtype}
