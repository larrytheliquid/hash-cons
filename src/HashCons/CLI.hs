module HashCons.CLI where
import Data.Text.IO hiding ( putStrLn )
import Prelude hiding ( readFile )
import System.IO hiding ( readFile )
import System.Environment
import HashCons.Term
import HashCons.BiMap
import HashCons.Parser
import HashCons.Printer

run :: IO ()
run = do
  args <- getArgs
  hashConsFile (head args)

hashConsFile :: FilePath -> IO ()
hashConsFile file = do
  code <- readFile file
  case parseFile code of
    Left error -> do
      putStrLn "Parse error:"
      putStrLn $ show error

    Right expr -> do
      -- putStrLn "Parsed!"
      pp 2 expr
      -- putStrLn $ show $ count expr
      -- let g = snd $ runNodeM expr
      -- pp 0 g
      -- putStrLn $ show $ size g
