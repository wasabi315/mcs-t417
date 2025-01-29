module T417.Syntax where

import Data.Functor
import Data.List
import Data.Maybe
import Prettyprinter
import StrictList as SL
import T417.Common

--------------------------------------------------------------------------------

data Term
  = Var VarName
  | Type
  | Kind
  | App Term Term
  | Lam VarName Term Term
  | Pi VarName Term Term
  | Const ConstName [Term]
  | TLoc (Located Term)
  deriving stock (Show)

type Type = Term

data Def = Def
  { name :: ConstName,
    params :: [(VarName, Type)],
    retTy :: Type,
    body :: Maybe (Term) -- Nothing for primitives
  }
  deriving stock (Show)

newtype Defs = Defs {unDefs :: [Def]}
  deriving newtype (Show)

--------------------------------------------------------------------------------

prettyTerm :: Term -> Doc ann
prettyTerm = \case
  Var x -> pretty x
  Type -> "*"
  Kind -> "@"
  App m n ->
    "%" <> parens (prettyTerm m) <> parens (prettyTerm n)
  Lam x m n ->
    "$" <> pretty x <> ":" <> parens (prettyTerm m) <> "." <> parens (prettyTerm n)
  Pi x m n ->
    "?" <> pretty x <> ":" <> parens (prettyTerm m) <> "." <> parens (prettyTerm n)
  Const c ms ->
    pretty c <> brackets (mconcat (punctuate comma (map (parens . prettyTerm) ms)))
  TLoc (Located {value}) -> prettyTerm value

instance Pretty Term where
  pretty = prettyTerm
  {-# INLINE pretty #-}

prettyDef :: Def -> Doc ann
prettyDef Def {..} =
  "def2"
    <> line
    <> vsep (params <&> \(x, ty) -> pretty x <> line <> pretty ty)
    <> line
    <> pretty name
    <> line
    <> maybe "#" pretty body
    <> line
    <> pretty retTy
    <> line
    <> "edef2"

instance Pretty Def where
  pretty = prettyDef
  {-# INLINE pretty #-}

instance Pretty Defs where
  pretty (Defs defs) = concatWith (\x y -> x <> line <> line <> y) (pretty <$> defs)
  {-# INLINE pretty #-}

--------------------------------------------------------------------------------

alphaEq :: [VarName] -> [VarName] -> Term -> Term -> Bool
alphaEq vs vs' = \cases
  (Var v) (Var v') -> case (elemIndex v vs, elemIndex v' vs') of
    (Just i, Just i') -> i == i'
    (Nothing, Nothing) -> v == v'
    _ -> False
  Type Type -> True
  Kind Kind -> True
  (App m n) (App m' n') -> alphaEq vs vs' m m' && alphaEq vs vs' n n'
  (Lam x m n) (Lam x' m' n') -> alphaEq vs vs' m m' && alphaEq (x : vs) (x' : vs') n n'
  (Pi x m n) (Pi x' m' n') -> alphaEq vs vs' m m' && alphaEq (x : vs) (x' : vs') n n'
  (Const c ms) (Const c' ns) -> c == c' && and (zipWith (alphaEq vs vs') ms ns)
  (TLoc m) (TLoc n) -> alphaEq vs vs' m.value n.value
  (TLoc m) n -> alphaEq vs vs' m.value n
  m (TLoc n) -> alphaEq vs vs' m n.value
  _ _ -> False

--------------------------------------------------------------------------------

rename :: VarName -> VarName -> Term -> Term
rename from to = \case
  Var x
    | x == from -> Var to
    | otherwise -> Var x
  Type -> Type
  Kind -> Kind
  App m n -> App (rename from to m) (rename from to n)
  t@(Lam x m n)
    | x == from -> t
    | otherwise -> Lam x (rename from to m) (rename from to n)
  t@(Pi x m n)
    | x == from -> t
    | otherwise -> Pi x (rename from to m) (rename from to n)
  Const c ms -> Const c (map (rename from to) ms)
  TLoc (Located {pos, value}) -> TLoc (Located pos (rename from to value))

substMany :: [(VarName, Term)] -> Term -> Term
substMany s = \case
  t@(Var x) -> fromMaybe t $ lookup x s
  Type -> Type
  Kind -> Kind
  App m n -> App (substMany s m) (substMany s n)
  Lam x m n ->
    let x' = freshen x
     in Lam x' (substMany s m) (substMany s (rename x x' n))
  Pi x m n ->
    let x' = freshen x
     in Pi x' (substMany s m) (substMany s (rename x x' n))
  Const c ms -> Const c (map (substMany s) ms)
  TLoc (Located {pos, value}) -> TLoc (Located pos (substMany s value))

subst :: VarName -> Term -> Term -> Term
subst from to = substMany [(from, to)]

data Nf
  = NVar VarName Spine
  | NType
  | NKind
  | NLam VarName Nf Nf
  | NPi VarName Nf Nf
  | NConst ConstName Spine ~Nf
  | NPrim ConstName Spine
  deriving stock (Show)

data Spine
  = SNil
  | SConstApp (SL.List Nf)
  | SApp Spine Nf
  deriving stock (Show)

forceConst :: Nf -> Nf
forceConst = \case
  NVar x sp -> NVar x (forceConstSpine sp)
  NType -> NType
  NKind -> NKind
  NLam x m n -> NLam x (forceConst m) (forceConst n)
  NPi x m n -> NPi x (forceConst m) (forceConst n)
  NConst _ _ m -> forceConst m
  NPrim c sp -> NPrim c (forceConstSpine sp)

forceConstSpine :: Spine -> Spine
forceConstSpine = \case
  SNil -> SNil
  SConstApp ms -> SConstApp $ forceConst <$> ms
  SApp sp m -> SApp (forceConstSpine sp) (forceConst m)

fromNf :: Nf -> Term
fromNf = \case
  NVar x sp -> fromNfSpineVar x sp
  NType -> Type
  NKind -> Kind
  NLam x m n -> Lam x (fromNf m) (fromNf n)
  NPi x m n -> Pi x (fromNf m) (fromNf n)
  NConst c sp _ -> fromNfSpineConst c sp
  NPrim c sp -> fromNfSpineConst c sp

fromNfSpineVar :: VarName -> Spine -> Term
fromNfSpineVar x = \case
  SNil -> Var x
  SConstApp _ -> error "impossible"
  SApp sp m -> App (fromNfSpineVar x sp) (fromNf m)

fromNfSpineConst :: ConstName -> Spine -> Term
fromNfSpineConst c = \case
  SNil -> Const c []
  SConstApp ms -> Const c $ SL.toListReversed $ SL.mapReversed fromNf ms
  SApp sp m -> App (fromNfSpineConst c sp) (fromNf m)

nf :: [(ConstName, Def)] -> Term -> Nf
nf defs = go
  where
    go = \case
      Var x -> NVar x SNil
      Type -> NType
      Kind -> NKind
      App m n -> go m $$ go n
      Lam x m n -> NLam x (go m) (go n)
      Pi x m n -> NPi x (go m) (go n)
      Const c ms ->
        let Def {..} = fromJust $ lookup c defs
            nfs = SL.mapReversed (nf defs) $ SL.fromListReversed ms
         in case body of
              Nothing -> NPrim c (SConstApp nfs)
              Just body' ->
                NConst
                  c
                  (SConstApp nfs)
                  $ go
                  $ substMany (zipWith (\(x, _) t -> (x, t)) params ms) body'
      TLoc (Located {..}) -> go value

instance Applicable Nf Nf Nf where
  m $$ n = go m
    where
      go = \case
        NLam x _ m' -> substNf x n m'
        NVar x sp -> NVar x (SApp sp n)
        NPrim c sp -> NPrim c (SApp sp n)
        NConst c sp m' -> NConst c (SApp sp n) (go m')
        _ -> error "impossible"
  {-# INLINE ($$) #-}

instance Applicable Nf Spine Nf where
  ($$) m = go
    where
      go = \case
        SNil -> m
        SConstApp _ -> error "impossible"
        SApp sp n -> go sp $$ n
  {-# INLINE ($$) #-}

renameNf :: VarName -> VarName -> Nf -> Nf
renameNf from to = \case
  NVar x sp
    | x == from -> NVar to (renameSpine from to sp)
    | otherwise -> NVar x (renameSpine from to sp)
  NType -> NType
  NKind -> NKind
  t@(NLam x m n)
    | x == from -> t
    | otherwise -> NLam x (renameNf from to m) (renameNf from to n)
  t@(NPi x m n)
    | x == from -> t
    | otherwise -> NPi x (renameNf from to m) (renameNf from to n)
  NConst c sp m -> NConst c (renameSpine from to sp) (renameNf from to m)
  NPrim c sp -> NPrim c (renameSpine from to sp)

renameSpine :: VarName -> VarName -> Spine -> Spine
renameSpine from to = \case
  SNil -> SNil
  SConstApp ms -> SConstApp $ renameNf from to <$> ms
  SApp sp m -> SApp (renameSpine from to sp) (renameNf from to m)

substNf :: VarName -> Nf -> Nf -> Nf
substNf from to = \case
  NVar x sp
    | x == from -> to $$ substSpine from to sp
    | otherwise -> NVar x (substSpine from to sp)
  NType -> NType
  NKind -> NKind
  NLam x m n ->
    let x' = freshen x
     in NLam x' (substNf from to m) (substNf from to (renameNf x x' n))
  NPi x m n ->
    let x' = freshen x
     in NPi x' (substNf from to m) (substNf from to (renameNf x x' n))
  NConst c sp m -> NConst c (substSpine from to sp) (substNf from to m)
  NPrim c sp -> NPrim c (substSpine from to sp)

substSpine :: VarName -> Nf -> Spine -> Spine
substSpine from to = \case
  SNil -> SNil
  SConstApp ms -> SConstApp $ substNf from to <$> ms
  SApp sp m -> SApp (substSpine from to sp) (substNf from to m)

data ConvMode = Rigid | Flex Int

nalphaEq :: ConvMode -> [VarName] -> [VarName] -> Nf -> Nf -> Bool
nalphaEq cm vs vs' = \cases
  (NVar x sp) (NVar x' sp') -> case (elemIndex x vs, elemIndex x' vs') of
    (Just i, Just i') -> i == i' && nalphaEqSpine cm vs vs' sp sp'
    (Nothing, Nothing) -> x == x' && nalphaEqSpine cm vs vs' sp sp'
    _ -> False
  NType NType -> True
  NKind NKind -> True
  (NLam x m n) (NLam x' m' n') -> nalphaEq cm vs vs' m m' && nalphaEq cm (x : vs) (x' : vs') n n'
  (NPi x m n) (NPi x' m' n') -> nalphaEq cm vs vs' m m' && nalphaEq cm (x : vs) (x' : vs') n n'
  (NPrim c sp) (NPrim c' sp') -> c == c' && nalphaEqSpine cm vs vs' sp sp'
  (NConst c sp m) (NConst c' sp' m') -> case cm of
    Rigid
      | c == c' -> nalphaEqSpine (Flex 32) vs vs' sp sp' || nalphaEq Rigid vs vs' m m'
      | otherwise -> nalphaEq cm vs vs' m m'
    Flex 0
      | c == c' -> nalphaEqSpine (Flex 0) vs vs' sp sp'
      | otherwise -> False
    Flex n
      | c == c' -> nalphaEqSpine (Flex n) vs vs' sp sp'
      | otherwise -> nalphaEq (Flex (n - 1)) vs vs' m m'
  (NConst _ _ m) m' -> case cm of
    Rigid -> nalphaEq cm vs vs' m m'
    Flex 0 -> False
    Flex n -> nalphaEq (Flex (n - 1)) vs vs' m m'
  m (NConst _ _ m') -> case cm of
    Rigid -> nalphaEq cm vs vs' m m'
    Flex 0 -> False
    Flex n -> nalphaEq (Flex (n - 1)) vs vs' m m'
  _ _ -> False

nalphaEqSpine :: ConvMode -> [VarName] -> [VarName] -> Spine -> Spine -> Bool
nalphaEqSpine cm vs vs' = \cases
  SNil SNil -> True
  (SConstApp ms) (SConstApp ns) -> nalphaEqs cm vs vs' ms ns
  (SApp sp m) (SApp sp' m') -> nalphaEqSpine cm vs vs' sp sp' && nalphaEq cm vs vs' m m'
  _ _ -> False

nalphaEqs :: ConvMode -> [VarName] -> [VarName] -> SL.List Nf -> SL.List Nf -> Bool
nalphaEqs cm vs vs' = \cases
  SL.Nil SL.Nil -> True
  (SL.Cons m ms) (SL.Cons m' ms') -> nalphaEqs cm vs vs' ms ms' && nalphaEq cm vs vs' m m'
  _ _ -> False

-- nf :: [(ConstName, Def)] -> Term -> Term
-- nf defs = go
--   where
--     go = \case
--       Var x -> Var x
--       Type -> Type
--       Kind -> Kind
--       App m n -> case whnf defs m of
--         Lam x _ n' -> go (subst x n n')
--         m' -> App (go m') (go n)
--       Lam x m n -> Lam x (go m) (go n)
--       Pi x m n -> Pi x (go m) (go n)
--       Const c ms ->
--         let Def {..} = fromJust $ lookup c defs
--             _ = assert (length params == length ms) ()
--          in case body of
--               Nothing -> Const c (map go ms)
--               Just body' -> go $ substMany (zipWith (\(x, _) t -> (x, t)) params ms) body'
--       TLoc (Located {..}) -> go value

-- whnf :: [(ConstName, Def)] -> Term -> Term
-- whnf defs = go
--   where
--     go = \case
--       Var x -> Var x
--       Type -> Type
--       Kind -> Kind
--       App m n -> case go m of
--         Lam x _ n' -> go (subst x n n')
--         m' -> App m' n
--       t@Lam {} -> t
--       t@Pi {} -> t
--       Const c ms ->
--         let Def {..} = fromJust $ lookup c defs
--             _ = assert (length params == length ms) ()
--          in case body of
--               Nothing -> Const c (map go ms)
--               Just body' -> go $ substMany (zipWith (\(x, _) t -> (x, t)) params ms) body'
--       TLoc (Located {..}) -> go value
