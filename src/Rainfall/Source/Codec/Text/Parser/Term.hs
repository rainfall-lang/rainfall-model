
module Rainfall.Source.Codec.Text.Parser.Term where
import Rainfall.Source.Codec.Text.Parser.Base
import Rainfall.Source.Exp.Term

-- import Text.Parsec                      ((<?>))
import qualified Text.Parsec            as P
import Data.Maybe


pTerm :: Parser (Term RL)
pTerm
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
 , do   pTermArg ]



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

 , do   -- Party
        pParty  >>= return . MParty

 , do   -- '{' Term,* '}'
        pPunc "{"
        ms      <- flip P.sepEndBy1 (pPunc ",") pTerm
        pPunc "}"
        return  $ MSet ms

 , do   -- Record
        pTermRecord
 ]


 -- | Parser for a record term.
pTermRecord :: Parser (Term RL)
pTermRecord
 = do   -- '[' (Lbl '=' Term),* ']'
        pPunc "["
        (ls, ms) <- fmap unzip
                 $  flip P.sepEndBy1 (pPunc ",")
                 $  do  l       <- pLbl
                        pPunc "="
                        m       <- pTerm
                        return  (l, m)
        pPunc "]"
        return  $ MRecord ls ms
