module HashCons.CLI where
import System.IO
import HashCons.Term
import HashCons.Parser

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
      putStrLn $ show expr
      putStrLn ""


