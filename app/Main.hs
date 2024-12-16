module Main where

import Control.Exception
import Data.Text.IO qualified as T
import Syntax
import System.Exit

orDie :: (Exception e) => Either e a -> IO a
orDie = flip either pure \e -> putStrLn (displayException e) >> exitFailure

main :: IO ()
main = do
  src <- T.getContents
  ast <- orDie $ parseText "stdin" src
  T.putStrLn $ pretty ast
