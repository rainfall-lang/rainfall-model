
module Rainfall.Source.Codec.Text.Parser.Base where
import Rainfall.Source.Exp
import Rainfall.Source.Codec.Text.Token
import qualified Text.Parsec                    as P
import qualified Text.Parsec.Pos                as P
import qualified Text.Lexer.Inchworm.Source     as IW


------------------------------------------------------------------------------------------ Types --
type Parser a   = P.Parsec [At Token] () a
type RL         = IW.Range IW.Location


------------------------------------------------------------------------------ Location Handling --
-- | Get the current position in the source stream.
locHere :: Parser IW.Location
locHere
 = do   sp      <- P.getPosition
        let loc =  IW.Location (P.sourceLine sp) (P.sourceColumn sp)
        return  $ loc


-- | Get the location of a token.
locOfTok :: At Token -> P.SourcePos
locOfTok (At (IW.Range (Location l c) _) _)
 = P.newPos "file" l c


------------------------------------------------------------------------------ Primitive Parsers --
-- | Parse the given token.
pTok :: Token -> Parser ()
pTok tMatch
 = pTokOf $ \tNext -> if tNext == tMatch then Just () else Nothing


-- | Parse a token that matches the given function.
pTokOf :: (Token -> Maybe a) -> Parser a
pTokOf fMatch
 = do   pTokOfInput fMatch


-- | Parse a token from the input stream.
pTokOfInput :: (Token -> Maybe a) -> Parser a
pTokOfInput fMatch
 = do   (_aTok, x)
         <- P.token show locOfTok $ \aTok@(At _r tok)
         -> case fMatch tok of
               Nothing -> Nothing
               Just x  -> Just (aTok, x)

        return x


----------------------------------------------------------------------------------- Name Parsers --
-- | Parser for a keyword.
pKey :: String -> Parser ()
pKey s = pTok (KKey s)

-- | Parser for punctuation.
pPunc :: String -> Parser ()
pPunc s = pTok (KPunc s)

-- | Parser for a variable name.
pVar :: Parser Name
pVar    = pTokOf $ \case { KVar s -> Just (Name s); _ -> Nothing }

-- | Parser for a constructor name.
pCon :: Parser Name
pCon    = pTokOf $ \case { KCon s -> Just (Name s); _ -> Nothing }

-- | Parser for a symbol name.
pSym :: Parser Name
pSym    = pTokOf $ \case { KSym s -> Just (Name s); _ -> Nothing }

-- | Parser for a match variable.
pBind :: Parser Name
pBind   = pTokOf $ \case { KMatch s -> Just (Name s); _ -> Nothing }

-- | Parser for a primitive name.
pPrm :: Parser Name
pPrm    = pTokOf $ \case { KPrm s -> Just (Name s); _ -> Nothing }

-- | Parser for a primitive with this specific name.
pPrmOf :: String -> Parser ()
pPrmOf t = pTokOf $ \case { KPrm s | s == t -> Just (); _ -> Nothing }

-- | Parser for a record or variant label.
pLbl :: Parser Name
pLbl    = pTokOf $ \case { KVar s -> Just (Name s); _ -> Nothing }

-- | Parser for a natural number.
pNat :: Parser Integer
pNat    = pTokOf $ \case { KNat n -> Just n; _ -> Nothing }

-- | Parser for a Haskell-style string.
pText :: Parser String
pText   = pTokOf $ \case { KText t -> Just t; _ -> Nothing }

-- | Parser for a party literal.
pParty :: Parser Name
pParty  = pTokOf $ \case { KParty s -> Just (Name s); _ -> Nothing }
