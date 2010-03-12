module Narradar.Utils.Parse (module Text.ParserCombinators.Parsec, module Narradar.Utils.Parse) where

import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language( emptyDef )

-- ------------------------------
-- General purpose Parsec lexer
-- ------------------------------

lexer  = P.makeTokenParser emptyDef

whiteSpace= P.whiteSpace lexer
lexeme    = P.lexeme lexer
symbol    = P.symbol lexer
natural   = P.natural lexer
parens    = P.parens lexer
dot       = P.dot lexer
comma     = P.comma lexer
semi      = P.semi lexer
identifier= P.identifier lexer
reserved  = P.reserved lexer
reservedOp= P.reservedOp lexer
commaSep  = P.commaSep lexer
stringLiteral = P.stringLiteral lexer
