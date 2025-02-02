module T417.Evaluation where

import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.Maybe
import StrictList qualified as SL
import T417.Common
import T417.Syntax

--------------------------------------------------------------------------------

data Value
  = VVar VarName Spine
  | VConst ConstName Spine ~Value
  | VPrim ConstName Spine
  | VType
  | VKind
  | VLam VType Closure
  | VPi VType Closure
  deriving stock (Show)

data Spine
  = SNil
  | SConstApp (SL.List Value)
  | SApp Spine Value
  deriving stock (Show)

data TopClosure = TopClosure [VarName] TopEnv Term
  deriving stock (Show)

data Closure = Closure VarName TopEnv LocalEnv Term
  deriving stock (Show)

type VType = Value

type TopEnv = HashMap ConstName TopClosure

type LocalEnv = HashMap VarName Value

--------------------------------------------------------------------------------

eval :: TopEnv -> LocalEnv -> Term -> Value
eval tenv lenv = \case
  Var x -> fromJust $ HM.lookup x lenv
  Type -> VType
  Kind -> VKind
  App m n -> eval tenv lenv m $$ eval tenv lenv n
  Lam x m n -> VLam (eval tenv lenv m) $ Closure x tenv lenv n
  Pi x m n -> VPi (eval tenv lenv m) $ Closure x tenv lenv n
  Const c ms ->
    let vs = eval tenv lenv <$> ms
     in case HM.lookup c tenv of
          Nothing -> VPrim c (SConstApp vs)
          Just t -> VConst c (SConstApp vs) (t $$ vs)
  TLoc (Located {..}) -> eval tenv lenv value

instance Applicable Closure Value Value where
  -- strict in the argument
  Closure x tenv lenv m $$ n = eval tenv (HM.insert x n lenv) m
  {-# INLINE ($$) #-}

instance Applicable (Lazy Closure) Value Value where
  -- lazy in the argument
  Lazy (Closure x tenv lenv m) $$ ~n = eval tenv (HM.insert x n lenv) m
  {-# INLINE ($$) #-}

instance Applicable TopClosure (SL.List Value) Value where
  -- assume that the length of xs and vs are the same
  -- strict in the arguments
  TopClosure xs tenv m $$ vs = eval tenv (HM.fromList (zip xs (SL.toListReversed vs))) m
  {-# INLINE ($$) #-}

instance Applicable (Lazy TopClosure) [Value] Value where
  -- lazy in the arguments
  Lazy (TopClosure xs tenv m) $$ vs = eval tenv (HM.fromList (zip xs (reverse vs))) m
  {-# INLINE ($$) #-}

instance Applicable Spine Value Spine where
  sp $$ v = SApp sp v
  {-# INLINE ($$) #-}

instance Applicable Value Value Value where
  m $$ n = go m
    where
      go = \case
        VLam _ m' -> m' $$ n
        VVar x sp -> VVar x (sp $$ n)
        VConst c sp m' -> VConst c (sp $$ n) (go m')
        VPrim c sp -> VPrim c (sp $$ n)
        _ -> error "application of non-function"
  {-# INLINE ($$) #-}

--------------------------------------------------------------------------------

data UnfoldTop = UnfoldTop | KeepTop

quote :: UnfoldTop -> LocalEnv -> Value -> Term
quote unf lenv = \case
  VVar x sp -> quoteSpineVar unf lenv x sp
  VConst c sp m -> case unf of
    UnfoldTop -> quote unf lenv m
    KeepTop -> quoteSpineConst unf lenv c sp
  VPrim c sp -> quoteSpineConst unf lenv c sp
  VType -> Type
  VKind -> Kind
  VLam m n@(Closure (freshen -> x) _ _ _) ->
    let v = VVar x SNil
     in Lam x (quote unf lenv m) (quote unf (HM.insert x v lenv) $ n $$ v)
  VPi a b@(Closure (freshen -> x) _ _ _) ->
    let v = VVar x SNil
     in Pi x (quote unf lenv a) (quote unf (HM.insert x v lenv) $ b $$ v)

quoteSpineVar :: UnfoldTop -> LocalEnv -> VarName -> Spine -> Term
quoteSpineVar unf lvl x = \case
  SNil -> Var x
  SConstApp _ -> error "quoteSpineVar: SConstApp"
  SApp sp m -> App (quoteSpineVar unf lvl x sp) (quote unf lvl m)

quoteSpineConst :: UnfoldTop -> LocalEnv -> ConstName -> Spine -> Term
quoteSpineConst unf lvl c = \case
  SNil -> error "quoteSpineConst: SNil"
  SConstApp vs -> Const c $ quote unf lvl <$> vs
  SApp sp m -> App (quoteSpineConst unf lvl c sp) (quote unf lvl m)

--------------------------------------------------------------------------------
-- βδ-conversion

data ConvMode = Rigid | Flex Int

bdConv :: ConvMode -> Value -> Value -> Bool
bdConv cm = \cases
  (VVar x sp) (VVar x' sp') -> x == x' && bdConvSpine cm sp sp'
  VType VType -> True
  VKind VKind -> True
  (VLam _ m@(Closure x _ _ _)) (VLam _ m') ->
    let v = VVar (freshen x) SNil
     in bdConv cm (m $$ v) (m' $$ v)
  (VPi a b@(Closure x _ _ _)) (VPi a' b') ->
    let v = VVar (freshen x) SNil
     in bdConv cm a a' && bdConv cm (b $$ v) (b' $$ v)
  (VPrim c sp) (VPrim c' sp') -> c == c' && bdConvSpine cm sp sp'
  (VConst c sp m) (VConst c' sp' m') -> case cm of
    Rigid
      | c == c' -> bdConvSpine (Flex 32) sp sp' || bdConv Rigid m m'
      | otherwise -> bdConv Rigid m m'
    Flex n
      | c == c' -> bdConvSpine (Flex n) sp sp'
      | n == 0 -> False
      | otherwise -> bdConv (Flex (n - 1)) m m'
  (VConst _ _ m) m' -> case cm of
    Rigid -> bdConv Rigid m m'
    Flex 0 -> False
    Flex n -> bdConv (Flex (n - 1)) m m'
  m (VConst _ _ m') -> case cm of
    Rigid -> bdConv Rigid m m'
    Flex 0 -> False
    Flex n -> bdConv (Flex (n - 1)) m m'
  _ _ -> False

bdConvSpine :: ConvMode -> Spine -> Spine -> Bool
bdConvSpine cm = \cases
  SNil SNil -> True
  (SConstApp vs) (SConstApp vs') -> bdConvs cm vs vs'
  (SApp sp v) (SApp sp' v') -> bdConvSpine cm sp sp' && bdConv cm v v'
  _ _ -> False

bdConvs :: ConvMode -> SL.List Value -> SL.List Value -> Bool
bdConvs cm = \cases
  SL.Nil SL.Nil -> True
  (SL.Cons v vs) (SL.Cons v' vs') -> bdConvs cm vs vs' && bdConv cm v v'
  _ _ -> False
