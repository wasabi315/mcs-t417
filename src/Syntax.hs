module Syntax where

import Control.Monad
import Data.Char
import Data.List
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Lazy qualified as TL
import Data.Text.Lazy.Builder (Builder)
import Data.Text.Lazy.Builder qualified as B
import Data.Text.Lazy.Builder.Int qualified as B
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
  name <- takeWhile1P Nothing ((||) <$> isAlphaNum <*> (== '_'))
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

--------------------------------------------------------------------------------
-- Prettyprinter

ppTerm :: Term -> Builder
ppTerm (Located _ t) = ppTerm' t

ppTerm' :: Term' -> Builder
ppTerm' = \case
  Var x -> B.fromText x
  Type -> "*"
  Kind -> "@"
  App m n -> "%(" <> ppTerm m <> ")(" <> ppTerm n <> ")"
  Lam x m n -> "$" <> B.fromText x <> ":(" <> ppTerm m <> ").(" <> ppTerm n <> ")"
  Pi x m n -> "?" <> B.fromText x <> ":(" <> ppTerm m <> ").(" <> ppTerm n <> ")"
  Const c ms ->
    B.fromText c
      <> "["
      <> mconcat (intersperse "," (map (\m -> "(" <> ppTerm m <> ")") ms))
      <> "]"

ppDef :: Def -> Builder
ppDef Def {..} =
  mconcat $
    intersperse "\n" $
      concat @[]
        [ [ "def2",
            B.decimal (length params)
          ],
          concatMap (\(x, m) -> [B.fromText x, ppTerm m]) params,
          [ B.fromText name,
            ppTerm body,
            ppTerm retTy,
            "edef2"
          ]
        ]

pretty :: [Def] -> Text
pretty = TL.toStrict . B.toLazyText . mconcat . intersperse "\n\n" . map ppDef
