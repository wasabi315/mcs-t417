module Main where

import Control.Exception
import Data.Text.IO qualified as T
import System.Exit
import T417.Parser
import T417.Verifier

orDie :: (Exception e) => Either e a -> IO a
orDie = flip either pure \e -> putStrLn (displayException e) >> exitFailure

main :: IO ()
main = do
  src <- T.readFile "bezout_script"
  rules <- orDie $ parseRules "bezout_script" src
  verify rules
