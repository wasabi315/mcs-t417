module T417.Common
  ( Located (..),
    VarName (..),
    ConstName (..),
    freshen,
    propriocept,
    Applicable (..),
  )
where

import Data.Hashable
import Data.String
import Data.Text (Text)
import Data.Text qualified as T
import Data.Unique
import Prettyprinter
import System.IO.Unsafe
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

newtype VarName = VarName {unVarName :: Text}
  deriving newtype (Show, Eq, Ord, Pretty, IsString, Hashable)

newtype ConstName = ConstName {unConstName :: Text}
  deriving newtype (Show, Eq, Ord, Pretty, IsString, Hashable)

freshen :: VarName -> VarName
freshen (VarName x) =
  propriocept \u -> VarName $ "#" <> x <> T.pack (show $ hashUnique u)

propriocept :: (Unique -> a) -> a
propriocept f = unsafePerformIO $ f <$> newUnique

--------------------------------------------------------------------------------

infixl 5 $$

class Applicable f a b | f a -> b where
  ($$) :: f -> a -> b

instance Applicable (a -> b) a b where
  f $$ x = f x
  {-# INLINE ($$) #-}
