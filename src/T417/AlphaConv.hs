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
  | ALam ATerm AClosure
  | APi ATerm AClosure
  | AConst ConstName (SL.List ATerm)
  deriving stock (Show)

type AType = ATerm

data ATopClosure where
  ATopClosure :: [(VarName, AType, a)] -> Term -> ATopClosure

data AClosure = AClosure VarName [(VarName, ATerm)] Term
  deriving stock (Show)

instance Pretty ATerm where
  pretty a = pretty (fromATerm a)

instance Applicable ATerm ATerm ATerm where
  m $$ n = AApp m n
  {-# INLINE ($$) #-}

toATerm :: [(VarName, ATerm)] -> Term -> ATerm
toATerm env = \case
  Var x -> fromMaybe (AVar x) $ lookup x env
  Type -> AType
  Kind -> AKind
  App m n -> toATerm env m $$ toATerm env n
  Lam x m n -> ALam (toATerm env m) (AClosure x env n)
  Pi x m n -> APi (toATerm env m) (AClosure x env n)
  Const c ms -> AConst c $ SL.mapReversed (toATerm env) $ SL.fromListReversed ms
  TLoc (Located {..}) -> toATerm env value

instance Applicable ATopClosure [ATerm] ATerm where
  ATopClosure xs m $$ ns = toATerm (zipWith (\(x, _, _) n -> (x, n)) xs (reverse ns)) m
  {-# INLINE ($$) #-}

instance Applicable AClosure ATerm ATerm where
  AClosure x env m $$ n = toATerm ((x, n) : env) m
  {-# INLINE ($$) #-}

fromATerm :: ATerm -> Term
fromATerm = \case
  AVar x -> Var x
  AType -> Type
  AKind -> Kind
  AApp m n -> App (fromATerm m) (fromATerm n)
  ALam m n@(AClosure x _ _) ->
    Lam x (fromATerm m) (fromATerm $ n $$ AVar x)
  APi m n@(AClosure x _ _) ->
    Pi x (fromATerm m) (fromATerm $ n $$ AVar x)
  AConst c ms -> Const c $ SL.toListReversed $ SL.mapReversed fromATerm ms

alphaConv :: ATerm -> ATerm -> Bool
alphaConv = \cases
  (AVar x) (AVar x') -> x == x'
  AType AType -> True
  AKind AKind -> True
  (AApp m n) (AApp m' n') -> alphaConv m m' && alphaConv n n'
  (ALam m n@(AClosure x _ _)) (ALam m' n') -> alphaConv m m' && alphaConv (n $$ AVar x) (n' $$ AVar x)
  (APi m n@(AClosure x _ _)) (APi m' n') -> alphaConv m m' && alphaConv (n $$ AVar x) (n' $$ AVar x)
  (AConst c ms) (AConst c' ns) -> c == c' && alphaConvs ms ns
  _ _ -> False

alphaConvs :: SL.List ATerm -> SL.List ATerm -> Bool
alphaConvs = \cases
  SL.Nil SL.Nil -> True
  (SL.Cons m ms) (SL.Cons n ns) -> alphaConvs ms ns && alphaConv m n
  _ _ -> False
