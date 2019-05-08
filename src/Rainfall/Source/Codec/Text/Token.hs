
module Rainfall.Source.Codec.Text.Token where
import Text.Lexer.Inchworm.Char


data Token
        = KBra
        | KKet
        | KVar String
        | KCon String
        | KInt Integer
        deriving Show

data Located a
        = Located FilePath (Range Location) a


