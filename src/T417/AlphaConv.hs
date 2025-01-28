module T417.AlphaConv where

import Data.Maybe
import Prettyprinter
import StrictList qualified as SL
import T417.Common
import T417.Syntax

--------------------------------------------------------------------------------

data ATerm
  = AVar VarName
  | AType
  | AKind
  | AApp ATerm ATerm
  | ALam VarName ATerm AClosure
  | APi VarName ATerm AClosure
  | AConst ConstName (SL.List ATerm)
  deriving stock (Show)

type AType = ATerm

data AClosure = AClosure VarName [(VarName, ATerm)] Term
  deriving stock (Show)

instance Pretty ATerm where
  pretty a = pretty (fromATerm a)

toATerm :: [(VarName, ATerm)] -> Term -> ATerm
toATerm env = \case
  Var x -> fromMaybe (AVar x) $ lookup x env
  Type -> AType
  Kind -> AKind
  App m n -> AApp (toATerm env m) (toATerm env n)
  Lam x m n -> ALam x (toATerm env m) (AClosure x env n)
  Pi x m n -> APi x (toATerm env m) (AClosure x env n)
  Const c ms -> AConst c $ SL.mapReversed (toATerm env) $ SL.fromListReversed ms
  TLoc (Located {..}) -> toATerm env value

instance Applicable AClosure ATerm ATerm where
  AClosure x env m $$ n = toATerm ((x, n) : env) m
  {-# INLINE ($$) #-}

fromATerm :: ATerm -> Term
fromATerm = \case
  AVar x -> Var x
  AType -> Type
  AKind -> Kind
  AApp m n -> App (fromATerm m) (fromATerm n)
  ALam x m n ->
    Lam x (fromATerm m) (fromATerm $ n $$ AVar x)
  APi x m n ->
    Pi x (fromATerm m) (fromATerm $ n $$ AVar x)
  AConst c ms -> Const c $ SL.toListReversed $ SL.mapReversed fromATerm ms

aalphaEq :: ATerm -> ATerm -> Bool
aalphaEq = \cases
  (AVar x) (AVar x') -> x == x'
  AType AType -> True
  AKind AKind -> True
  (AApp m n) (AApp m' n') -> aalphaEq m m' && aalphaEq n n'
  (ALam x m n) (ALam _ m' n') -> aalphaEq m m' && aalphaEq (n $$ AVar x) (n' $$ AVar x)
  (APi x m n) (APi _ m' n') -> aalphaEq m m' && aalphaEq (n $$ AVar x) (n' $$ AVar x)
  (AConst c ms) (AConst c' ns) -> c == c' && aalphaEqs ms ns
  _ _ -> False

aalphaEqs :: SL.List ATerm -> SL.List ATerm -> Bool
aalphaEqs = \cases
  SL.Nil SL.Nil -> True
  (SL.Cons m ms) (SL.Cons n ns) -> aalphaEqs ms ns && aalphaEq m n
  _ _ -> False
