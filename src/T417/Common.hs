module T417.Common
  ( Located (..),
    VarName (..),
    ConstName (..),
    freshen,
  )
where

import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)
import Prettyprinter
import Text.Megaparsec

--------------------------------------------------------------------------------
-- Location information

data Located a = Located
  { pos :: SourcePos,
    value :: a
  }
  deriving stock (Functor, Foldable, Traversable)

instance (Show a) => Show (Located a) where
  showsPrec d (Located _ x) = showsPrec d x

instance (Eq a) => Eq (Located a) where
  Located _ x == Located _ y = x == y

instance (Ord a) => Ord (Located a) where
  compare (Located _ x) (Located _ y) = compare x y

instance (Pretty a) => Pretty (Located a) where
  pretty (Located _ x) = pretty x

--------------------------------------------------------------------------------

newtype VarName = VarName {unVarName :: Char}
  deriving newtype (Show, Eq, Ord, Pretty)

newtype ConstName = ConstName {unConstName :: Text}
  deriving newtype (Show, Eq, Ord, Pretty)

varNameCandiates :: Set VarName
varNameCandiates = S.fromDistinctAscList $ map VarName "ABCDEFGHIJKLMNOPQRSTUVWXYZabcedfghijklmnopqrstuvwxyz"
{-# NOINLINE varNameCandiates #-}

freshen :: [VarName] -> VarName -> VarName
freshen used x
  | x `elem` used = S.findMax $ foldr S.delete varNameCandiates used
  | otherwise = x
