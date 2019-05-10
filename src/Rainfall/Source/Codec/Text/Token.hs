
module Rainfall.Source.Codec.Text.Token
        ( Location (..)
        , Token    (..)
        , At       (..))
where
import Text.Lexer.Inchworm.Char

-- | A source token.
data Token
        = KEND                          -- ^ Indicate end of input.
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

