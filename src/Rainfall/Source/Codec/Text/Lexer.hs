
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
 $ alts [ fmap (stamp KInfix) $ munchPred Nothing
                (\_ix c -> elem c infixChars)
                (\str   -> if elem str infixOps
                                then Just str else Nothing)

        , fmap (stamp KPunc)
           $ munchWord (\ix c -> ix == 0 && elem c puncs)

        , fmap (stamp KVar) $ munchPred Nothing
                (\ix c -> case ix of
                                0 -> Char.isLower c
                                _ -> Char.isAlpha c)
                (\str   -> if not $ elem str keywords
                                then Just str else Nothing)

        , fmap (stamp KKey) $ munchPred Nothing
                (\_ix c -> Char.isLower c)
                (\str   -> if elem str keywords
                                then Just str else Nothing)


        , fmap (stamp KCon) $ munchWord $ \ix c
          -> case ix of
                0       -> Char.isUpper c
                _       -> Char.isAlpha c

        , fmap  (stamp KPrm) $ munchPred Nothing
                (\ix c -> case ix of
                                0   -> c == '#'
                                _   -> Char.isAlphaNum c || c == '\'')
                (\('#' : rest) -> Just rest)

        , fmap  (stamp KSym) $ munchPred Nothing
                (\ix c -> case ix of
                                0   -> c == '\''
                                _   -> Char.isAlphaNum c || c == '\'')
                (\('\'' : rest) -> Just rest)

        , fmap  (stamp KMatch) $ munchPred Nothing
                (\ix c -> case ix of
                                0   -> c == '?'
                                1   -> Char.isLower c
                                _   -> Char.isAlphaNum c)
                (\('?' : rest) -> Just rest)

        , fmap  (stamp KParty) $ munchPred Nothing
                (\ix c -> case ix of
                                0   -> c == '!'
                                1   -> Char.isUpper c
                                _   -> Char.isAlphaNum c)
                (\('!' : rest) -> Just rest)

        , fmap (stamp KNat)     $ scanInteger
        , fmap (stamp KChar)    $ scanHaskellChar
        , fmap (stamp KText)    $ scanHaskellString

        , fmap (stamp KCOMMENT) $ scanHaskellCommentLine
        , fmap (stamp KCOMMENT) $ scanHaskellCommentBlock
        ]
 where  -- Stamp a token with source location information.
        stamp k (l, t)
          = At l (k t)

        puncs
         = [ '(', ')', '[', ']', '{', '}'
           , ':', ',', '=' ]

        infixChars
         = [ '-', '+', '<', '>', '='
           , '∧', '∨', '∪'
           , '≤', '≥'
           , '∖', '∈', '∉' ]

        infixOps
         = [ "<", "<=", "≤"
           , ">", ">=", "≥"
           , "∧", "∨", "∪", "∪+", "∖", "∈", "∉"
           , "-", "+"]

        keywords
         = [ "fact"
           , "rule", "await", "and", "to"
           , "scenario", "do", "add", "fire", "rules", "dump"
           , "where"
           , "select", "first", "last"
           , "consume", "none"
           , "gain", "check"
           , "say",  "by", "obs", "use", "num" ]


-- | Scan a Rainfall source file, producing tokens,
--   final location, and leftover chars.
scanSource :: FilePath -> String -> ([At Token], Location, String)
scanSource filePath str
 = scanString str (scanner filePath)

