module T417.Evaluation where

import Data.Foldable
import Data.Maybe
import StrictList qualified as SL
import T417.Common
import T417.Syntax
import T417.Value

--------------------------------------------------------------------------------

type TopEnv = [(ConstName, Value)]

type LocalEnv = [(VarName, Value)]

eval :: TopEnv -> LocalEnv -> Term -> Value
eval tenv lenv = \case
  Var x -> fromJust $ lookup x lenv
  Type -> VType
  Kind -> VKind
  App m n -> eval tenv lenv m $$ eval tenv lenv n
  Lam x m n -> VLam x (eval tenv lenv m) \v -> eval tenv ((x, v) : lenv) n
  Pi x m n -> VPi x (eval tenv lenv m) \v -> eval tenv ((x, v) : lenv) n
  Const c ms ->
    let vs = SL.mapReversed (eval tenv lenv) $ SL.fromListReversed ms
     in VConst c (SConstApp vs) (foldl' ($$) (fromJust $ lookup c tenv) vs)
  TLoc (Located {..}) -> eval tenv lenv value

($$) :: Value -> Value -> Value
($$) = \cases
  (VLam _ _ m) n -> m n
  (VVar x sp) n -> VVar x (sp `SApp` n)
  (VConst c sp m) n -> VConst c (sp `SApp` n) (m $$ n)
  _ _ -> error "application of non-function"

--------------------------------------------------------------------------------

data UnfoldTop = UnfoldTop | KeepTop

quote :: UnfoldTop -> LocalEnv -> Value -> Term
quote unf lenv = \case
  VVar x sp -> quoteSpineVar unf lenv x sp
  VConst c sp m -> case unf of
    UnfoldTop -> quote unf lenv m
    KeepTop -> quoteSpineConst unf lenv c sp
  VType -> Type
  VKind -> Kind
  VLam (freshen -> x) m n ->
    let v = VVar x SNil
     in Lam x (quote unf lenv m) (quote unf ((x, v) : lenv) $ n v)
  VPi (freshen -> x) a b ->
    let v = VVar x SNil
     in Pi x (quote unf lenv a) (quote unf ((x, v) : lenv) $ b v)

quoteSpineVar :: UnfoldTop -> LocalEnv -> VarName -> Spine -> Term
quoteSpineVar unf lvl x = \case
  SNil -> Var x
  SConstApp _ -> error "quoteSpineVar: SConstApp"
  SApp sp m -> App (quoteSpineVar unf lvl x sp) (quote unf lvl m)

quoteSpineConst :: UnfoldTop -> LocalEnv -> ConstName -> Spine -> Term
quoteSpineConst unf lvl c = \case
  SNil -> error "quoteSpineConst: SNil"
  SConstApp vs -> Const c $ SL.toListReversed $ SL.mapReversed (quote unf lvl) vs
  SApp sp m -> App (quoteSpineConst unf lvl c sp) (quote unf lvl m)

--------------------------------------------------------------------------------
-- β-conversion

data ConvMode = Rigid | Flex | Full

conv :: LocalEnv -> ConvMode -> Value -> Value -> Bool
conv lenv cm = \cases
  (VVar x sp) (VVar x' sp') -> x == x' && convSpine lenv cm sp sp'
  VType VType -> True
  VKind VKind -> True
  (VLam (freshen -> x) _ m) (VLam _ _ m') ->
    let v = VVar x SNil
     in conv ((x, v) : lenv) cm (m v) (m' v)
  (VPi (freshen -> x) a b) (VPi _ a' b') ->
    let v = VVar x SNil
     in conv lenv cm a a' && conv ((x, v) : lenv) cm (b v) (b' v)
  (VConst c sp m) (VConst c' sp' m') -> case cm of
    Rigid
      | c == c' -> convSpine lenv Flex sp sp' || conv lenv Full m m'
      | otherwise -> conv lenv Rigid m m'
    Flex
      | c == c' -> convSpine lenv Flex sp sp'
      | otherwise -> False
    Full -> conv lenv Full m m'
  (VConst _ _ m) m' -> case cm of
    Rigid -> conv lenv Rigid m m'
    Flex -> False
    Full -> conv lenv Full m m'
  m (VConst _ _ m') -> case cm of
    Rigid -> conv lenv Rigid m m'
    Flex -> False
    Full -> conv lenv Full m m'
  _ _ -> False

convSpine :: LocalEnv -> ConvMode -> Spine -> Spine -> Bool
convSpine lvl cm = \cases
  SNil SNil -> True
  (SConstApp vs) (SConstApp vs') -> convs lvl cm vs vs'
  (SApp sp v) (SApp sp' v') -> convSpine lvl cm sp sp' && conv lvl cm v v'
  _ _ -> False

convs :: LocalEnv -> ConvMode -> SL.List Value -> SL.List Value -> Bool
convs lvl cm = \cases
  SL.Nil SL.Nil -> True
  (SL.Cons v vs) (SL.Cons v' vs') -> convs lvl cm vs vs' && conv lvl cm v v'
  _ _ -> False
