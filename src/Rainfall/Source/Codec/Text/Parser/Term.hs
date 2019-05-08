
module Rainfall.Source.Codec.Text.Parser.Term where
import Rainfall.Source.Codec.Text.Parser.Base
import Rainfall.Source.Exp.Term

-- import Text.Parsec                      ((<?>))
import qualified Text.Parsec            as P



-- | Parser for a term argument.
pTermArg :: Parser (Term RL)
pTermArg
 = P.choice
 [ do   -- Var
        n <- pVar
        return $ MVar $ Bound n

 , do   -- Con
        pCon    >>= return . MCon

 , do   -- Syn
        pSym    >>= return . MSym

 , do   -- Int
        pInt    >>= return . MInt

 ]