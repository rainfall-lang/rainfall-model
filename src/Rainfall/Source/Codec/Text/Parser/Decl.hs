
module Rainfall.Source.Codec.Text.Parser.Decl where
import Rainfall.Source.Codec.Text.Parser.Term
import Rainfall.Source.Codec.Text.Parser.Base
-- import Rainfall.Source.Codec.Text.Token
import Rainfall.Source.Exp
import qualified Text.Parsec            as P


------------------------------------------------------------------------------------------- Decl --
-- Parser for top-level declarations.
pDecls :: Parser [Decl RL]
pDecls = P.many pDecl

-- Parser for a top-level declaration.
pDecl  :: Parser (Decl RL)
pDecl
 = P.choice
 [ do   -- 'fact' Con '[' (Lbl ',' Type),* ']'
        pKey "fact"
        n       <- pCon
        pPunc "["
        fs      <- flip P.sepBy (pPunc ",")
                $  do   l       <- pLbl
                        pPunc ":"
                        n       <- pCon
                        return  (l, TCon n)
        pPunc "]"
        return $ DeclFact n fs

 , do   -- Rule
        rule    <- pRule
        return  $ DeclRule rule

 ]


------------------------------------------------------------------------------------------- Rule --
-- 'rule' Var 'await' Pattern{'and'+} 'to' Term
pRule  :: Parser (Rule RL)
pRule
 = do   pKey "rule"
        nRule   <- pVar
        pKey "await"
        ps      <- flip P.sepBy1 (pKey "and") pMatch
        pKey "to"
        mBody   <- pTerm
        return  $  Rule nRule ps mBody


-- | @Name '[' (Label '=' Pattern),* ']'@
pMatch :: Parser (Match RL)
pMatch
 = do   nFact   <- pCon
        pPunc "["
        ps      <- flip P.sepBy (pPunc ",")
                $  do   l       <- pLbl
                        pPunc   "="
                        p       <- pGatherPat
                        return  (l, p)
        pPunc "]"
        gain    <- pGain
        return  $ Match
                { matchBind     = Nothing
                , matchGather   = GatherPat nFact ps Nothing
                , matchSelect   = SelectAny
                , matchConsume  = ConsumeNone
                , matchGain     = gain }


pGatherPat :: Parser (GatherPat RL)
pGatherPat
 = P.choice
 [ do   n       <- pBind
        return  $ GatherPatBind n

 , do   m       <- pTerm
        return  $ GatherPatEq m
 ]


pGain :: Parser (Gain RL)
pGain
 = P.choice
 [ do   pKey "gain"
        mGain   <- pTerm
        return  $  GainTerm mGain

 , do   pKey "check"
        mCheck  <- pTerm
        return  $  GainCheck mCheck

 , do   return GainNone ]


