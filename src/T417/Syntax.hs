module T417.Syntax where

import Control.Exception (assert)
import Data.Functor
import Data.List
import Data.Maybe
import Prettyprinter
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
  | TLoc {-# UNPACK #-} (Located Term)
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
    pretty c <> brackets (hsep (punctuate comma (map (parens . prettyTerm) ms)))
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

nf :: [(ConstName, Def)] -> Term -> Term
nf defs = go
  where
    go = \case
      Var x -> Var x
      Type -> Type
      Kind -> Kind
      App m n -> case whnf defs m of
        Lam x _ n' -> go (subst x n n')
        m' -> App (go m') (go n)
      Lam x m n -> Lam x (go m) (go n)
      Pi x m n -> Pi x (go m) (go n)
      Const c ms ->
        let Def {..} = fromJust $ lookup c defs
            _ = assert (length params == length ms) ()
            Just body' = body
         in go $ substMany (zipWith (\(x, _) t -> (x, t)) params ms) body'
      TLoc (Located {..}) -> go value

whnf :: [(ConstName, Def)] -> Term -> Term
whnf defs = go
  where
    go = \case
      Var x -> Var x
      Type -> Type
      Kind -> Kind
      App m n -> case go m of
        Lam x _ n' -> go (subst x n n')
        m' -> App m' n
      t@Lam {} -> t
      t@Pi {} -> t
      Const c ms ->
        let Def {..} = fromJust $ lookup c defs
            _ = assert (length params == length ms) ()
            Just body' = body
         in go $ substMany (zipWith (\(x, _) t -> (x, t)) params ms) body'
      TLoc (Located {..}) -> go value
