module Main where

import System.Environment
import Control.Exception
import Data.Text.IO qualified as T
import System.Exit
import T417.Parser
import T417.Verifier

orDie :: (Exception e) => Either e a -> IO a
orDie = flip either pure \e -> putStrLn (displayException e) >> exitFailure

main :: IO ()
main = do
  [path] <- getArgs
  src <- T.readFile path
  rules <- orDie $ parseRules path src
  verify rules
