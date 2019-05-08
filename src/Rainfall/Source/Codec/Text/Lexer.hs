
module Rainfall.Source.Codec.Text.Lexer
        (scanSource)
where
import Rainfall.Source.Codec.Text.Token
import Text.Lexer.Inchworm
import Text.Lexer.Inchworm.Char
import qualified Data.Char      as Char


-- | Scanner for Rainfall source.
scanner :: FilePath
        -> Scanner IO Location [Char] (At Token)
scanner _fileName
 = skip Char.isSpace
 $ alts [ fmap (stamp KPunc)
           $ munchWord (\ix c -> ix == 0 && elem c puncs)

        , fmap (stamp KKey) $ munchPred Nothing
                (\_ix c -> Char.isLower c)
                (\str   -> if elem str keywords then Just str else Nothing)

        , fmap (stamp KVar) $ munchWord $ \ix c
          -> case ix of
                0       -> Char.isLower c
                _       -> Char.isAlpha c

        , fmap (stamp KCon) $ munchWord $ \ix c
          -> case ix of
                0       -> Char.isUpper c
                _       -> Char.isAlpha c

        , fmap (stamp KSym) $ munchWord $ \ix c
          -> case ix of
                0       -> c == '\''
                _       -> Char.isAlphaNum c

        , fmap (stamp KMatch) $ munchWord $ \ix c
          -> case ix of
                0       -> c == '?'
                1       -> Char.isLower c
                _       -> Char.isAlphaNum c

        , fmap (stamp KInt)     $ scanInteger
        , fmap (stamp KChar)    $ scanHaskellChar
        , fmap (stamp KText)    $ scanHaskellString

        , fmap (stamp KParty)
          $ munchWord $ \ix c
          -> case ix of
                0       -> c == '!'
                1       -> Char.isUpper c
                _       -> Char.isAlphaNum c

        ]
 where  -- Stamp a token with source location information.
        stamp k (l, t)
          = At l (k t)

        puncs
         = [ '(', ')', '[', ']', '{', '}'
           , ':', ',', '=' ]

        keywords
         = [ "fact"
           , "rule", "await", "and", "to"
           , "select", "consume", "gain", "none"
           , "say",  "by", "obs", "use", "num" ]


-- | Scan a Rainfall source file, producing tokens,
--   final location, and leftover chars.
scanSource :: FilePath -> String -> ([At Token], Location, String)
scanSource filePath str
 = scanString str (scanner filePath)

