module T417.Parser where

import Control.Monad
import Data.Char
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void
import GHC.IsList
import T417.Common
import T417.Rule
import T417.Syntax
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

--------------------------------------------------------------------------------

type Parser = Parsec Void Text

located :: Parser a -> Parser (Located a)
located p = Located <$> getSourcePos <*> p

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

decimal :: (Num a) => Parser a
decimal = lexeme L.decimal

parens, brackets :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")
brackets = between (symbol "[") (symbol "]")

pVarName :: Parser VarName
pVarName = VarName . T.singleton <$> lexeme letterChar

pConstName :: Parser ConstName
pConstName = lexeme do
  name <- takeWhile1P Nothing \c -> isAlphaNum c || c == '_' || c == '-' || c == '.'
  guard (T.length name >= 2)
  pure $ ConstName name

--------------------------------------------------------------------------------

pTerm :: Parser Term
pTerm = TLoc <$> located pTerm'

pTerm' :: Parser Term
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
        pure $ Const c (fromList args),
      Var <$> pVarName
    ]

pDef :: Parser Def
pDef = do
  symbol "def2"
  n <- decimal
  params <- replicateM n ((,) <$> pVarName <*> pTerm)
  name <- pConstName
  body <- (Nothing <$ symbol "#") <|> Just <$> pTerm
  retTy <- pTerm
  symbol "edef2"
  pure Def {..}

parseDefs :: FilePath -> Text -> Either (ParseErrorBundle Text Void) Defs
parseDefs = parse (fmap Defs (many pDef) <* optional (symbol "END") <* eof)

--------------------------------------------------------------------------------

pRule :: Parser Rule
pRule =
  (RSort <$ symbol "sort")
    <|> (RVar <$> (symbol "var" *> decimal) <*> pVarName)
    <|> (RWeak <$> (symbol "weak" *> decimal) <*> decimal <*> pVarName)
    <|> (RForm <$> (symbol "form" *> decimal) <*> decimal)
    <|> (RAppl <$> (symbol "appl" *> decimal) <*> decimal)
    <|> (RAbst <$> (symbol "abst" *> decimal) <*> decimal)
    <|> (RConv <$> (symbol "conv" *> decimal) <*> decimal)
    <|> try (RDefpr <$> (symbol "defpr" *> decimal) <*> decimal <*> pConstName)
    <|> (RDef <$> (symbol "def" *> decimal) <*> decimal <*> pConstName)
    <|> do
      symbol "inst"
      i <- decimal
      n <- decimal
      js <- replicateM n decimal
      p <- decimal
      pure $ RInst i (fromList js) p
    <|> (RCp <$> (symbol "cp" *> decimal))
    <|> (RSp <$> (symbol "sp" *> decimal) <*> decimal)

pRules :: Parser Rules
pRules = do
  rs <- some $ liftM2 (,) decimal pRule
  pure $ Rules rs

parseRules :: FilePath -> Text -> Either (ParseErrorBundle Text Void) Rules
parseRules = parse (pRules <* optional (symbol "-1") <* eof)
