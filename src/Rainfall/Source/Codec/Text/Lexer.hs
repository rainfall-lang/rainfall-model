
module Rainfall.Source.Codec.Text.Lexer
        (scanner)
where
import Rainfall.Source.Codec.Text.Token
import Text.Lexer.Inchworm
import Text.Lexer.Inchworm.Char
import qualified Data.Char      as Char


-- | Scanner for a lispy language.
scanner :: FilePath
        -> Scanner IO Location [Char] (Located Token)
scanner fileName
 = skip Char.isSpace
 $ alts [ fmap (stamp id)   $ accept '(' KBra
        , fmap (stamp id)   $ accept ')' KKet
        , fmap (stamp KInt) $ scanInteger
        , fmap (stamp KVar)
          $ munchWord (\ix c -> if ix == 0 then Char.isLower c
                                           else Char.isAlpha c)
        , fmap (stamp KCon)
          $ munchWord (\ix c -> if ix == 0 then Char.isUpper c
                                           else Char.isAlpha c)
        ]
 where  -- Stamp a token with source location information.
        stamp k (l, t)
          = Located fileName l (k t)
