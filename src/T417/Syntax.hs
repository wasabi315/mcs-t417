module T417.Syntax where

import Data.Traversable
import Prettyprinter
import T417.Common

--------------------------------------------------------------------------------

newtype Ix = Ix Int
  deriving newtype (Eq, Ord, Show, Num, Pretty)

data Term
  = Var Ix
  | Type
  | Kind
  | App Term Term
  | Lam VarName Term Term
  | Pi VarName Term Term
  | Const ConstName [Term]
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

prettyTerm :: [VarName] -> Term -> Doc ann
prettyTerm vars = \case
  Var (Ix x) -> pretty (vars !! x)
  Type -> "*"
  Kind -> "@"
  App m n ->
    "%" <> parens (prettyTerm vars m) <> parens (prettyTerm vars n)
  Lam (freshen vars -> x) m n ->
    "$" <> pretty x <> ":" <> parens (prettyTerm vars m) <> "." <> parens (prettyTerm (x : vars) n)
  Pi (freshen vars -> x) m n ->
    "?" <> pretty x <> ":" <> parens (prettyTerm vars m) <> "." <> parens (prettyTerm (x : vars) n)
  Const c ms ->
    pretty c <> brackets (hsep (punctuate comma (map (parens . prettyTerm vars) ms)))

prettyDef :: Def -> Doc ann
prettyDef Def {..} =
  "def2"
    <> line
    <> vsep paramDocs
    <> pretty name
    <> line
    <> maybe "#" (prettyTerm vars) body
    <> line
    <> prettyTerm vars retTy
    <> line
    <> "edef2"
  where
    (vars, paramDocs) =
      mapAccumL
        (\acc (freshen vars -> x, ty) -> (x : acc, pretty x <> line <> prettyTerm acc ty))
        []
        params
