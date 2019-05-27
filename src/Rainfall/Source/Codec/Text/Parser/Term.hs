
module Rainfall.Source.Codec.Text.Parser.Term where
import Rainfall.Source.Codec.Text.Parser.Base
import Rainfall.Source.Exp.Term
import qualified Text.Parsec            as P
import Data.Maybe


-- | Parser for a term.
pTerm :: Parser (Term RL)
pTerm = pTermInfix5


-- | Parse infix application at precedence 5.
pTermInfix5 :: Parser (Term RL)
pTermInfix5
 = do   m       <- pTermInfix4
        P.choice
         [ do   op      <- pInfixOf ["∨", "∪", "∪+"]
                m'      <- pTermInfix5
                return  $  MInfix op m m'

         , do   return   m ]


-- | Parse infix application at precedence 4.
pTermInfix4 :: Parser (Term RL)
pTermInfix4
 = do   m       <- pTermInfix3
        P.choice
         [ do   op      <- pInfixOf ["∧", "∩"]
                m'      <- pTermInfix4
                return  $  MInfix op m m'

         , do   return   m ]


-- | Parse infix application at precedence 3.
pTermInfix3 :: Parser (Term RL)
pTermInfix3
 = do   m       <- pTermInfix2
        P.choice
         [ do   op      <- pInfixOf ["<", "<=", "≤", ">", ">=", "≥", "∈", "∉"]
                m'      <- pTermInfix3
                return  $  MInfix op m m'

         , do   return   m ]


-- | Parse infix application at precedence 2.
pTermInfix2 :: Parser (Term RL)
pTermInfix2
 = do   m       <- pTermInfix1
        P.choice
         [ do   op      <- pInfixOf ["+", "-", "∖"]
                m'      <- pTermInfix2
                return  $  MInfix op m m'

         , do   return   m ]


-- | Parse infix application at precedence 1.
pTermInfix1 :: Parser (Term RL)
pTermInfix1
 = do   m       <- pTermApp
        P.choice
         [ do   op      <- pInfixOf ["*", "/"]
                m'      <- pTermInfix1
                return  $  MInfix op m m'

         , do   return   m ]


-- | Parser for an application term.
pTermApp :: Parser (Term RL)
pTermApp
 = P.choice
 [ do   -- 'say' TermRecord ('by' Term)? ('obs' Term)? ('use' Term)? ('num' Term)?
        pKey "say"
        nFact   <- pCon
        mRecord <- pTermRecord
        mmBy    <- P.optionMaybe (do pKey "by";  m <- pTerm; return m)
        mmObs   <- P.optionMaybe (do pKey "obs"; m <- pTerm; return m)
        mmUse   <- P.optionMaybe (do pKey "use"; m <- pTerm; return m)
        mmNum   <- P.optionMaybe (do pKey "num"; m <- pTerm; return m)
        return  $  MKey (MKSay nFact)
                        [ MGTerm  $ mRecord
                        , MGTerms $ maybeToList mmBy
                        , MGTerms $ maybeToList mmObs
                        , MGTerms $ maybeToList mmUse
                        , MGTerms $ maybeToList mmNum ]

 , do   nPrm    <- pPrm
        msArg   <- P.many pTermArg
        return  $  MPrm nPrm $ map MGTerm msArg

 , do   pTermArg
 ]


-- | Parser for a term argument.
pTermArg :: Parser (Term RL)
pTermArg
 = P.choice
 [ do   -- Var
        n <- pVar
        return $ MVar $ Bound n

 , do   -- Syn
        pSym    >>= return . MSym

 , do   -- Nat
        pNat    >>= return . MNat

 , do   -- Text
        pText   >>= return . MText

 , do   -- Party
        pParty  >>= return . MParty

 , do   -- '{' Term,* '}'
        pPunc "{"
        ms      <- flip P.sepEndBy (pPunc ",") pTerm
        pPunc "}"
        return  $ MSet ms

 , do   -- Record
        pTermRecord

 , do   pPunc "("
        m       <- pTerm
        pPunc ")"
        return m
 ]


 -- | Parser for a record term.
pTermRecord :: Parser (Term RL)
pTermRecord
 = do   -- '[' (Lbl '=' Term),* ']'
        pPunc "["
        (ls, ms) <- fmap unzip
                 $  flip P.sepEndBy (pPunc ",")
                 $  do  l       <- pLbl
                        pPunc "="
                        m       <- pTerm
                        return  (l, m)
        pPunc "]"
        return  $ MRcd ls ms
