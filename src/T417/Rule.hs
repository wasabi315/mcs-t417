module T417.Rule where

import Data.Vector (Vector)
import Prettyprinter
import T417.Common

--------------------------------------------------------------------------------

newtype RuleIx = RuleIx Int
  deriving newtype (Eq, Ord, Show, Num, Pretty)

data Rule
  = RSort
  | RVar RuleIx VarName
  | RWeak RuleIx RuleIx VarName
  | RForm RuleIx RuleIx
  deriving stock (Show)

newtype Rules = Rules (Vector Rule)
  deriving newtype (Show)

prettyRule :: Rule -> Doc ann
prettyRule = \case
  RSort -> "sort"
  RVar i x -> "var" <+> pretty i <+> pretty x
  RWeak i j x -> "weak" <+> pretty i <+> pretty j <+> pretty x
  RForm i j -> "form" <+> pretty i <+> pretty j

instance Pretty Rule where
  pretty = prettyRule
  {-# INLINE pretty #-}

--------------------------------------------------------------------------------

-- -- Δ; Γ ⊢ M : N
-- data Judgment = Judgment
--   { delta :: [()],
--     gamma :: [(VarName, Type)],
--     term :: Term,
--     type_ :: Type
--   }

-- verify :: Vector Rule -> Maybe (Vector Judgment)
-- verify = undefined
