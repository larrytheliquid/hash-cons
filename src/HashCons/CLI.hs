module HashCons.CLI where
import System.IO
import System.Environment
import HashCons.Term
import HashCons.Parser
import HashCons.Printer

run :: IO ()
run = do
  args <- getArgs
  hashConsFile (head args)

hashConsFile :: FilePath -> IO ()
hashConsFile file = do
  code <- readFile file
  case parseFile file code of
    Left error -> do
      putStrLn "Parse error:"
      putStrLn $ formatParseError error

    Right expr -> do
      putStrLn $ "Parsed expression:"
      putStrLn ""
      pp expr

