module Text.ParserCombinators.Parsec.Tag where

import Control.Applicative
import Control.Monad
import Data.Char
import Data.Maybe
import Text.HTML.TagSoup
import Text.ParserCombinators.Parsec.Prim  hiding ((<|>), many)
import Text.ParserCombinators.Parsec.Combinator (many1)
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Applicative ()

type TagParser st = GenParser Tag st

myTagToken = tokenPrim show updatePosTag
updatePosTag s _ _ = incSourceColumn s 1


satisfy f = myTagToken (\ t -> if (f t) then Just t else Nothing)
tagOpenName  = satisfy . isTagOpenName
tagCloseName = satisfy . isTagCloseName
tagOpen  = satisfy isTagOpen
tagClose = satisfy isTagClose
tagText   = myTagToken (\tag -> case tag of
                                TagText _ -> Just tag
                                _         -> Nothing)
tag :: String -> TagParser st Tag
tag t = satisfy (~== t) <?> t

tag' :: (Tag -> Bool) -> TagParser st Tag
tag' t = satisfy t <?> "TAG"

tagP :: String -> TagParser st contents -> TagParser st contents
tagP t p = (do
  tag t
  result <- p
  skipMany tagText
  let closing_tag = head $ words $ tail $ init t
  tag' (== TagClose closing_tag) <?> closing_tag
  return result
  ) <?> t

anyTag :: TagParser st Tag
anyTag = myTagToken Just

elemTag :: Tag -> [Tag] -> Bool
elemTag tag = any (tag ~==)

oneOf ts  = satisfy (`elemTag` ts)
noneOf ts = satisfy (not . (`elemTag` ts))

skipTagP :: TagParser st Tag
skipTagP = do
  tag@(TagOpen name _) <- tagOpen
  skipMany ((tagText >> return ()) <|> (skipTagP >> return ()))
  tagCloseName name
  return tag

someTagP t k = (tagP t k <|> (skipTagP >> someTagP t k)) <* many skipTagP

skipTagNameP :: String -> TagParser st ()
skipTagNameP name = do
  tag name
  skipMany ((tagText >> return ()) <|> (skipTagP >> return ()))
  let closing_tag = head $ words $ tail $ init name
  tag' (== TagClose closing_tag) <?> closing_tag
  return ()

childrenP = do
  open@(TagOpen name _) <- tagOpen
  content <- many (many1 tagText <|> childrenP)
  close <- tagCloseName name
  return (open : concat content ++ [close])
