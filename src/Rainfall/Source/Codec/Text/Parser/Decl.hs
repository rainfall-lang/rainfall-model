
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
        DeclRule <$> pRule

 , do   -- Scenario
        DeclScenario <$> pScenario
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
        mPred   <- pWhere
        select  <- pSelect
        consume <- pConsume
        gain    <- pGain
        return  $ Match
                { matchGather   = GatherPat nFact ps mPred
                , matchSelect   = select
                , matchConsume  = consume
                , matchGain     = gain }


pWhere :: Parser (Maybe (Term RL))
pWhere
 = P.choice
 [ do   pKey "where"
        m       <- pTerm
        return  $ Just m

 , do   return  Nothing ]


pGatherPat :: Parser (GatherPat RL)
pGatherPat
 = P.choice
 [ do   n       <- pBind
        return  $ GatherPatBind n

 , do   m       <- pTerm
        return  $ GatherPatEq m
 ]


-- | Parse a select clause.
pSelect :: Parser (Select RL)
pSelect
 = P.choice
 [ do   pKey "select"
        P.choice
         [ do   pKey "any"
                return  $ SelectAny

         , do   pKey "first"
                mKey    <- pTerm
                return  $ SelectFirst mKey

         , do   pKey "last"
                mKey    <- pTerm
                return  $ SelectLast mKey
         ]

 , do   return  $ SelectAny
 ]


-- | Parse a consume clause.
pConsume :: Parser (Consume RL)
pConsume
 = P.choice
 [ do   pKey "consume"
        P.choice
         [ do   pKey "none"
                return  $ ConsumeNone

         , do   mWeight <- pTerm
                return  $ ConsumeWeight mWeight
         ]

 , do   return $ ConsumeWeight (MNat 1)  ]


-- | Parse a gain cause.
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


--------------------------------------------------------------------------------------- Scenario --
-- 'scenario' Var 'to' Action+
pScenario :: Parser (Scenario RL)
pScenario
 = do   pKey "scenario"
        nScn    <- pVar
        pKey "do"
        actions <- P.many pAction
        return  $ Scenario nScn actions


pAction :: Parser (Action RL)
pAction
 = P.choice
 [ do   pKey "add"
        mFoids  <- pTerm
        return  $ ActionAdd mFoids

 , do   pKey "fire"
        pKey "by"
        mAuth   <- pTerm
        pKey "rules"
        mRules  <- pTerm
        return  $ ActionFire mAuth mRules

 , do   pKey "dump"
        return  $ ActionDump
 ]

