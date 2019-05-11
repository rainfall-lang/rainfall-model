
module Rainfall.Source.Codec.Text.Token
        ( Location (..)
        , Range    (..)
        , Token    (..)
        , At       (..)
        , isKCOMMENT)
where
import Text.Lexer.Inchworm.Char

-- | A source token.
data Token
        = KEND                          -- ^ Indicate end of input.
        | KCOMMENT      String          -- ^ Capture source level comments.
        | KPunc         String          -- ^ Punctuation.
        | KVar          String          -- ^ Variable,          starts with lower case.
        | KCon          String          -- ^ Constructor,       starts with upper case.
        | KSym          String          -- ^ Symbol,            starts with apostrophe.
        | KPrm          String          -- ^ Primitive,         starts with '#'.
        | KMatch        String          -- ^ Match variable,    starts with question mark.
        | KNat          Integer         -- ^ Literal natural number.
        | KChar         Char            -- ^ Literal character, Haskell style.
        | KText         String          -- ^ Literal string, Haskell style.
        | KParty        String          -- ^ Literal party identifier.
        | KKey          String          -- ^ Keyword.
        deriving (Show, Eq)

data At a
        = At (Range Location) a
        deriving Show


-- | Check if this is a comment token.
isKCOMMENT :: Token -> Bool
isKCOMMENT kk
 = case kk of
        KCOMMENT{}      -> True
        _               -> False
