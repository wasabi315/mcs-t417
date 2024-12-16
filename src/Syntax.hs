module Syntax where

import Control.Monad
import Data.Char (isAlphaNum)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

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

--------------------------------------------------------------------------------
-- Abstract syntax tree

type VarName = Text

type ConstName = Text

type Term = Located Term'

data Term'
  = Var VarName
  | Type
  | Kind
  | App Term Term
  | Lam VarName Term Term
  | Pi VarName Term Term
  | Const ConstName [Term]
  deriving stock (Show)

data Def = Def
  { name :: ConstName,
    params :: [(VarName, Term)],
    retTy :: Term,
    body :: Term
  }
  deriving stock (Show)

--------------------------------------------------------------------------------
-- Parser

type Parser = Parsec Void Text

located :: Parser a -> Parser (Located a)
located p = Located <$> getSourcePos <*> p

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

decimal :: Parser Int
decimal = lexeme L.decimal

parens, brackets :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")
brackets = between (symbol "[") (symbol "]")

pVarName :: Parser VarName
pVarName = T.singleton <$> lexeme letterChar

pConstName :: Parser ConstName
pConstName = lexeme do
  name <- takeWhile1P Nothing isAlphaNum
  guard (T.length name >= 2)
  pure name

pTerm :: Parser Term
pTerm = located pTerm'

pTerm' :: Parser Term'
pTerm' =
  msum @[]
    [ Type <$ symbol "*",
      Kind <$ symbol "@",
      do
        char '%'
        m <- parens pTerm
        n <- parens pTerm
        pure $ App m n,
      do
        char '$'
        x <- pVarName
        symbol ":"
        m <- parens pTerm
        symbol "."
        n <- parens pTerm
        pure $ Lam x m n,
      do
        char '?'
        x <- pVarName
        symbol ":"
        m <- parens pTerm
        symbol "."
        n <- parens pTerm
        pure $ Pi x m n,
      try do
        c <- pConstName
        args <- brackets (parens pTerm `sepBy` symbol ",")
        pure $ Const c args,
      Var <$> pVarName
    ]

pDef :: Parser Def
pDef = do
  symbol "def2"
  n <- decimal
  params <- replicateM n ((,) <$> pVarName <*> pTerm)
  name <- pConstName
  body <- pTerm
  retTy <- pTerm
  symbol "edef2"
  pure Def {..}

parseText :: FilePath -> Text -> Either (ParseErrorBundle Text Void) [Def]
parseText = parse (many pDef <* eof)
