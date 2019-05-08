
module Rainfall.Source.Codec.Text.Parser.Decl where
import Rainfall.Source.Codec.Text.Parser.Base
import Rainfall.Source.Codec.Text.Token
import Rainfall.Source.Exp
import qualified Text.Parsec            as P


-- Parser for a top-level declaration.
pDecl :: Parser (Decl RL)
pDecl
 = P.choice
 [ do   pTok (KKey "fact")
        n       <- pCon
        pTok (KPunc "[")
        fs      <- flip P.sepBy (pTok (KPunc ","))
                $  do   l       <- pLbl
                        pTok (KPunc ":")
                        n       <- pCon
                        return  (l, TCon n)
        pTok (KPunc "]")
        return $ DeclFact n fs ]

