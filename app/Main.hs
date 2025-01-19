module Main where

import Control.Exception
import Data.Text.IO qualified as T
import Prettyprinter
import Prettyprinter.Util
import System.Exit
import T417.Parser

orDie :: (Exception e) => Either e a -> IO a
orDie = flip either pure \e -> putStrLn (displayException e) >> exitFailure

main :: IO ()
main = do
  src <- T.getContents
  defs <- orDie $ parseDefs "stdin" src
  putDocW 80 $ pretty defs
