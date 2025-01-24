module Main where

import Control.Exception
import Data.Foldable
import Data.Text.IO qualified as T
import Data.Vector qualified as V
import Prettyprinter
import Prettyprinter.Util
import System.Exit
import T417.Parser
import T417.Verifier

orDie :: (Exception e) => Either e a -> IO a
orDie = flip either pure \e -> putStrLn (displayException e) >> exitFailure

main :: IO ()
main = do
  src <- T.getContents
  rules <- orDie $ parseRules "stdin" src
  let jdgs = verify rules
  for_ @[] [0 .. V.length jdgs - 1] \i -> do
    putDocW 80 $ pretty i <+> pretty (jdgs V.! i)
    putStrLn ""
