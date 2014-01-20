{-# LANGUAGE OverloadedStrings #-}
module HashCons.Parser where
import HashCons.Term
import HashCons.Printer
import Prelude hiding ( pi , any , concat )
import qualified Prelude
import Data.Text hiding ( map )
import Data.Attoparsec.Text
import Data.Attoparsec.Combinator
import Data.Char
import Data.Functor.Identity (Identity)
import Text.Printf
import Control.Applicative

----------------------------------------------------------------------

ops = ["λ", "→", ":"]
nonIdent = ["(", ")"] ++ ops
nonIdentTxt = concat nonIdent

isIdent c = not (isSpace c || isControl c || any (c ==) nonIdentTxt)
identChar = satisfy isIdent

lexeme p = p <* skipSpace
parseToken = lexeme . string
parseOp = parseToken
parseIdent = lexeme $ many1 identChar
parseStringLit = lexeme $ char '"' *> many anyChar <* char '"'
parseParens p = lexeme $ char '(' *> p <* char ')'

----------------------------------------------------------------------

parseFile :: Text -> Either String Expr
parseFile txt = convertResult $ parse (skipSpace *> parseExpr <* skipSpace) txt

convertResult :: IResult Text Expr -> Either String Expr
convertResult (Done _ expr) = Right expr
convertResult (Fail _ _ error) = Left error
convertResult (Partial f) = convertResult $ f Data.Text.empty

----------------------------------------------------------------------

parseExpr :: Parser Expr
parseExpr = choice
  [ parseArr
  , parseAppsOrAtom
  , parsePis
  , parseLam
  ]

parseAtom :: Parser Expr
parseAtom = choice
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
  return $ pis (Prelude.concat nm_As) _B

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