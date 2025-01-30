module T417.Syntax where

import Data.Functor
import Data.String
import Prettyprinter
import StrictList qualified as SL
import T417.Common

--------------------------------------------------------------------------------

data Term
  = Var VarName
  | Type
  | Kind
  | App Term Term
  | Lam VarName Term Term
  | Pi VarName Term Term
  | Const ConstName (SL.List Term)
  | TLoc (Located Term)
  deriving stock (Show)

type Type = Term

instance IsString Term where
  fromString = Var . fromString
  {-# INLINE fromString #-}

instance Applicable Term Term Term where
  m $$ n = App m n
  {-# INLINE ($$) #-}

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
    pretty c
      <> brackets (mconcat (punctuate comma (SL.toListReversed $ SL.mapReversed (parens . prettyTerm) ms)))
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
