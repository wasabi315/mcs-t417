module T417.Presyntax where

import Data.Functor
import Data.List
import Prettyprinter
import T417.Common

--------------------------------------------------------------------------------
-- Surface syntax

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
    body :: Maybe Term -- Nothing for primitives
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

alphaEq :: Term -> Term -> Bool
alphaEq = go [] []
  where
    go e1 e2 = \cases
      (Var x) (Var y) -> elemIndex x e1 == elemIndex y e2
      Type Type -> True
      Kind Kind -> True
      (App m n) (App m' n') -> go e1 e2 m m' && go e1 e2 n n'
      (Lam x m n) (Lam y m' n') -> go e1 e2 m m' && go (x : e1) (y : e2) n n'
      (Pi x m n) (Pi y m' n') -> go e1 e2 m m' && go (x : e1) (y : e2) n n'
      (Const c ms) (Const d ns) -> c == d && and (zipWith (go e1 e2) ms ns)
      (TLoc m) (TLoc n) -> go e1 e2 m.value n.value
      (TLoc m) n -> go e1 e2 m.value n
      m (TLoc n) -> go e1 e2 m n.value
      _ _ -> False
{-# INLINE alphaEq #-}
