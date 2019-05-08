
module Rainfall.Source.Codec.Text.Token
        ( Location (..)
        , Token    (..)
        , Located  (..))
where
import Text.Lexer.Inchworm.Char

-- | A source token.
data Token
        = KPunc         String          -- ^ Punctuation.
        | KVar          String          -- ^ Variable,          starts with lower case.
        | KCon          String          -- ^ Constructor,       starts with upper case.
        | KSym          String          -- ^ Symbol,            starts with apostrophe.
        | KMatch        String          -- ^ Match variable,    starts with question mark.
        | KInteger      Integer         -- ^ Literal integer.
        | KChar         Char            -- ^ Literal character, Haskell style.
        | KString       String          -- ^ Literal string, Haskell style.
        | KParty        String          -- ^ Literal party identifier.
        | KKey          String          -- ^ Keyword.
        deriving Show

data Located a
        = Located FilePath (Range Location) a
        deriving Show

