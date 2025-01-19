module T417.Evaluation where

import Data.Maybe
import T417.Common
import T417.Syntax
import T417.Value

--------------------------------------------------------------------------------

type TopEnv = [(ConstName, Value)]

type LocalEnv = [Value]

eval :: TopEnv -> LocalEnv -> Term -> Value
eval tenv lenv = \case
  Var (Ix x) -> lenv !! x
  Type -> VType
  Kind -> VKind
  App m n -> eval tenv lenv m $$ eval tenv lenv n
  Lam x m n -> VLam x (eval tenv lenv m) \v -> eval tenv (v : lenv) n
  Pi x m n -> VPi x (eval tenv lenv m) \v -> eval tenv (v : lenv) n
  Const c ms ->
    let vs = map (eval tenv lenv) ms
     in VConst c (SConstApp vs) (foldl ($$) (fromJust $ lookup c tenv) vs)

($$) :: Value -> Value -> Value
($$) = \cases
  (VLam _ _ m) n -> m n
  (VVar x sp) n -> VVar x (sp `SApp` n)
  (VConst c sp m) n -> VConst c (sp `SApp` n) (m $$ n)
  _ _ -> error "application of non-function"

--------------------------------------------------------------------------------

data UnfoldTop = UnfoldTop | KeepTop

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl x) (Lvl y) = Ix (x - y - 1)

quote :: UnfoldTop -> Lvl -> Value -> Term
quote unf lvl = \case
  VVar x sp -> quoteSpineVar unf lvl (lvl2Ix lvl x) sp
  VConst c sp m -> case unf of
    UnfoldTop -> quote unf lvl m
    KeepTop -> quoteSpineConst unf lvl c sp
  VType -> Type
  VKind -> Kind
  VLam x m n -> Lam x (quote unf lvl m) (quote unf (lvl + 1) $ n (VVar lvl SNil))
  VPi x a b -> Pi x (quote unf lvl a) (quote unf (lvl + 1) $ b (VVar lvl SNil))

quoteSpineVar :: UnfoldTop -> Lvl -> Ix -> Spine -> Term
quoteSpineVar unf lvl x = \case
  SNil -> Var x
  SConstApp _ -> error "quoteSpineVar: SConstApp"
  SApp sp m -> App (quoteSpineVar unf lvl x sp) (quote unf lvl m)

quoteSpineConst :: UnfoldTop -> Lvl -> ConstName -> Spine -> Term
quoteSpineConst unf lvl c = \case
  SNil -> error "quoteSpineConst: SNil"
  SConstApp vs -> Const c (map (quote unf lvl) vs)
  SApp sp m -> App (quoteSpineConst unf lvl c sp) (quote unf lvl m)

--------------------------------------------------------------------------------
-- β-conversion

data ConvMode = Rigid | Flex | Full

conv :: Lvl -> ConvMode -> Value -> Value -> Bool
conv lvl cm = \cases
  (VVar x sp) (VVar x' sp') -> x == x' && convSpine lvl cm sp sp'
  VType VType -> True
  VKind VKind -> True
  (VLam _ _ m) (VLam _ _ m') ->
    let v = VVar lvl SNil
     in conv (lvl + 1) cm (m v) (m' v)
  (VPi _ a b) (VPi _ a' b') ->
    let v = VVar lvl SNil
     in conv lvl cm a a' && conv (lvl + 1) cm (b v) (b' v)
  (VConst c sp m) (VConst c' sp' m') -> case cm of
    Rigid
      | c == c' -> convSpine lvl Flex sp sp' || conv lvl Full m m'
      | otherwise -> conv lvl Rigid m m'
    Flex
      | c == c' -> convSpine lvl Flex sp sp'
      | otherwise -> False
    Full -> conv lvl Full m m'
  (VConst _ _ m) m' -> case cm of
    Rigid -> conv lvl Rigid m m'
    Flex -> False
    Full -> conv lvl Full m m'
  m (VConst _ _ m') -> case cm of
    Rigid -> conv lvl Rigid m m'
    Flex -> False
    Full -> conv lvl Full m m'
  _ _ -> False

convSpine :: Lvl -> ConvMode -> Spine -> Spine -> Bool
convSpine lvl cm = \cases
  SNil SNil -> True
  (SConstApp vs) (SConstApp vs') -> and $ zipWith (conv lvl cm) vs vs'
  (SApp sp v) (SApp sp' v') -> convSpine lvl cm sp sp' && conv lvl cm v v'
  _ _ -> False
