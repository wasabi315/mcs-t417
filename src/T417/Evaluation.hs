module T417.Evaluation where

import Data.Foldable
import Data.Maybe
import StrictList qualified as SL
import T417.Common
import T417.Syntax hiding (ConvMode (..), Spine (..))

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

type TopEnv = [(ConstName, TopClosure)]

type LocalEnv = [(VarName, Value)]

--------------------------------------------------------------------------------

eval :: TopEnv -> LocalEnv -> Term -> Value
eval tenv lenv = \case
  Var x -> fromJust $ lookup x lenv
  Type -> VType
  Kind -> VKind
  App m n -> eval tenv lenv m $$ eval tenv lenv n
  Lam x m n -> VLam (eval tenv lenv m) $ Closure x tenv lenv n
  Pi x m n -> VPi (eval tenv lenv m) $ Closure x tenv lenv n
  Const c ms ->
    let vs = SL.mapReversed (eval tenv lenv) $ SL.fromListReversed ms
     in case lookup c tenv of
          Nothing -> VPrim c (SConstApp vs)
          Just t -> VConst c (SConstApp vs) (t $$ toList vs)
  TLoc (Located {..}) -> eval tenv lenv value

instance Applicable Closure Value Value where
  Closure x tenv lenv m $$ n = eval tenv ((x, n) : lenv) m
  {-# INLINE ($$) #-}

instance Applicable TopClosure [Value] Value where
  -- assume that the length of xs and vs are the same
  TopClosure xs tenv m $$ vs = eval tenv (zip xs vs) m
  {-# INLINE ($$) #-}

instance Applicable Value Value Value where
  m $$ n = go m
    where
      go = \case
        VLam _ m' -> m' $$ n
        VVar x sp -> VVar x (sp `SApp` n)
        VConst c sp m' -> VConst c (sp `SApp` n) (m' $$ n)
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
     in Lam x (quote unf lenv m) (quote unf ((x, v) : lenv) $ n $$ v)
  VPi a b@(Closure (freshen -> x) _ _ _) ->
    let v = VVar x SNil
     in Pi x (quote unf lenv a) (quote unf ((x, v) : lenv) $ b $$ v)

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
-- βδ-conversion

data ConvMode = Rigid | Flex | Full

bdConv :: LocalEnv -> ConvMode -> Value -> Value -> Bool
bdConv lenv cm = \cases
  (VVar x sp) (VVar x' sp') -> x == x' && bdConvSpine lenv cm sp sp'
  VType VType -> True
  VKind VKind -> True
  (VLam _ m@(Closure (freshen -> x) _ _ _)) (VLam _ m') ->
    let v = VVar x SNil
     in bdConv ((x, v) : lenv) cm (m $$ v) (m' $$ v)
  (VPi a b@(Closure (freshen -> x) _ _ _)) (VPi a' b') ->
    let v = VVar x SNil
     in bdConv lenv cm a a' && bdConv ((x, v) : lenv) cm (b $$ v) (b' $$ v)
  (VConst c sp m) (VConst c' sp' m') -> case cm of
    Rigid
      | c == c' -> bdConvSpine lenv Flex sp sp' || bdConv lenv Full m m'
      | otherwise -> bdConv lenv Rigid m m'
    Flex
      | c == c' -> bdConvSpine lenv Flex sp sp'
      | otherwise -> False
    Full -> bdConv lenv Full m m'
  (VConst _ _ m) m' -> case cm of
    Rigid -> bdConv lenv Rigid m m'
    Flex -> False
    Full -> bdConv lenv Full m m'
  m (VConst _ _ m') -> case cm of
    Rigid -> bdConv lenv Rigid m m'
    Flex -> False
    Full -> bdConv lenv Full m m'
  _ _ -> False

bdConvSpine :: LocalEnv -> ConvMode -> Spine -> Spine -> Bool
bdConvSpine lvl cm = \cases
  SNil SNil -> True
  (SConstApp vs) (SConstApp vs') -> bdConvs lvl cm vs vs'
  (SApp sp v) (SApp sp' v') -> bdConvSpine lvl cm sp sp' && bdConv lvl cm v v'
  _ _ -> False

bdConvs :: LocalEnv -> ConvMode -> SL.List Value -> SL.List Value -> Bool
bdConvs lvl cm = \cases
  SL.Nil SL.Nil -> True
  (SL.Cons v vs) (SL.Cons v' vs') -> bdConvs lvl cm vs vs' && bdConv lvl cm v v'
  _ _ -> False
