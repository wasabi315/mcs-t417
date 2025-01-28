module T417.Rule where

import Data.Hashable
import Prettyprinter
import T417.Common

--------------------------------------------------------------------------------

newtype RuleIx = RuleIx Int
  deriving newtype (Eq, Ord, Show, Num, Pretty, Hashable)

data Rule
  = RSort
  | RVar RuleIx VarName
  | RWeak RuleIx RuleIx VarName
  | RForm RuleIx RuleIx
  | RAppl RuleIx RuleIx
  | RAbst RuleIx RuleIx
  | RConv RuleIx RuleIx
  | RDef RuleIx RuleIx ConstName
  | RDefpr RuleIx RuleIx ConstName
  | RInst RuleIx [RuleIx] Int
  | RCp RuleIx
  | RSp RuleIx Int
  deriving stock (Show)

newtype Rules = Rules [Rule]
  deriving newtype (Show)

prettyRule :: Rule -> Doc ann
prettyRule = \case
  RSort -> "sort"
  RVar i x -> "var" <+> pretty i <+> pretty x
  RWeak i j x -> "weak" <+> pretty i <+> pretty j <+> pretty x
  RForm i j -> "form" <+> pretty i <+> pretty j
  RAppl i j -> "appl" <+> pretty i <+> pretty j
  RAbst i j -> "abst" <+> pretty i <+> pretty j
  RConv i j -> "conv" <+> pretty i <+> pretty j
  RDef i j c -> "def" <+> pretty i <+> pretty j <+> pretty c
  RDefpr i j c -> "defpr" <+> pretty i <+> pretty j <+> pretty c
  RInst i js p ->
    "inst" <+> pretty i <+> pretty (length js) <+> hsep (map pretty js) <+> pretty p
  RCp i -> "cp" <+> pretty i
  RSp i j -> "sp" <+> pretty i <+> pretty j

instance Pretty Rule where
  pretty = prettyRule
  {-# INLINE pretty #-}

instance Pretty Rules where
  pretty (Rules rs) =
    vsep $ zipWith (\i r -> pretty i <+> pretty r) [0 :: Int ..] rs
  {-# INLINE pretty #-}
