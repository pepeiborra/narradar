module Text.ParserCombinators.Parsec.Tag where

import Data.Char
import Data.Maybe
import Text.HTML.TagSoup
import Text.ParserCombinators.Parsec.Prim
import Text.ParserCombinators.Parsec.Combinator
import Text.ParserCombinators.Parsec.Pos

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
  let closing_tag = tail $ init $ head $ words t
  tag' (== TagClose closing_tag) <?> closing_tag
  return result
  ) <?> t
anyTag :: TagParser st Tag
anyTag = myTagToken Just

elemTag :: Tag -> [Tag] -> Bool
elemTag tag = any (tag ~==)

oneOf ts  = satisfy (`elemTag` ts)
noneOf ts = satisfy (not . (`elemTag` ts))

childrenP = do
  open@(TagOpen name _) <- tagOpen
  content <- many (many1 tagText <|> childrenP)
  close <- tagCloseName name
  return (open : concat content ++ [close])

skipTill :: GenParser Tag st a -> GenParser Tag st a
skipTill end = go where
    go = try end <|> (anyTag >> go)
