module HashCons.Parser where
import HashCons.Term
import HashCons.Printer
import Prelude hiding (pi)
import Text.Parsec hiding ( label )
import Text.Parsec.Expr
import Text.Parsec.Token
import Data.Char
import Text.Parsec.Language
import Text.Parsec.Error
import Data.Functor.Identity (Identity)
import Text.Printf
import Control.Applicative

----------------------------------------------------------------------

ops = ["λ", "→", ":"]
nonIdent = ["(", ")"] ++ ops
keywords = []
identChar = satisfy (\c -> not (isSpace c || isControl c || elem c (concat nonIdent)))

def = emptyDef {
  commentStart = "{-"
, commentEnd = "-}"
, commentLine = "--"
, identStart = identChar
, identLetter = identChar
, opStart = oneOf (map head ops)
, opLetter = oneOf (concat ops)
, reservedOpNames = ops
, reservedNames = keywords
}

type ParserM a = ParsecT [Char] () Identity a

tokenizer = makeTokenParser def
parseOp = reservedOp tokenizer
parseKeyword = reserved tokenizer
parseIdent = identifier tokenizer
parseToken = symbol tokenizer
parseSpaces = whiteSpace tokenizer
parseStringLit = stringLiteral tokenizer
parseParens :: ParserM a -> ParserM a
parseParens = try . parens tokenizer

tryChoices xs = choice (map try xs)

----------------------------------------------------------------------

printCode :: String -> IO ()
printCode cd = case parseFile "." cd of
  Left error -> putStrLn (formatParseError error) >> putStrLn ""
  Right expr -> pp expr >> putStrLn ""

-- printCode :: String -> String
-- printCode cd = case parseFile "." cd of
--   Left error -> formatParseError error
--   Right expr -> pp expr

parseFile :: FilePath -> String -> Either ParseError Expr
parseFile = parse (parseSpaces >> (parseExpr <* eof))

-- Format error message so that Emacs' compilation mode can parse the
-- location information.
formatParseError :: ParseError -> String
formatParseError error = printf "%s:%i:%i:\n%s" file line col msg
  where
  file = sourceName . errorPos $ error
  line = sourceLine . errorPos $ error
  col = sourceColumn . errorPos $ error
  -- Copied from 'Show' instance for 'ParseError':
  -- http://hackage.haskell.org/packages/archive/parsec/latest/doc/html/src/Text-Parsec-Error.html#ParseError
  msg = showErrorMessages "or" "unknown parse error"
          "expecting" "unexpected" "end of input"
          (errorMessages error)

----------------------------------------------------------------------

parseExpr :: ParserM Expr
parseExpr = tryChoices
  [ parseArr
  , parseAppsOrAtom
  , parsePis
  , parseLam
  ]

parseAtom = tryChoices
  [ parseParens parseExpr
  , parseVar
  , parseLabel
  ]

----------------------------------------------------------------------

parseVar = var <$> parseIdent

parseLabel = label <$> parseStringLit

parseAppsOrAtom = apps <$> many1 parseAtom

----------------------------------------------------------------------

parsePiDomains = many1 $ parseParens $ do
  nms <- many1 parseIdent
  parseOp ":"
  _A <- parseExpr
  return $ map (\nm -> (nm , _A)) nms

parsePis = do
  nm_As <- parsePiDomains
  parseOp "→"
  _B <- parseExpr
  return $ pis (concat nm_As) _B

----------------------------------------------------------------------

parseArrDomain = do
  _A <- parseAppsOrAtom
  return (wildcard , _A)

parseArr = do
  (nm , _A) <- parseArrDomain
  parseOp "→"
  _B <- parseExpr
  return $ pi nm _A _B

----------------------------------------------------------------------

parseLam = do
  parseOp "λ"
  nms <- many1 parseIdent
  parseOp "→"
  bd <- parseExpr
  return $ lams nms bd

----------------------------------------------------------------------