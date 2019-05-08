
module Rainfall.Source.Codec.Text.Parser
        ( parseDecl
        , parseTerm)
where
import Rainfall.Source.Codec.Text.Parser.Decl
import Rainfall.Source.Codec.Text.Parser.Term
import Rainfall.Source.Codec.Text.Parser.Base
import Rainfall.Source.Codec.Text.Token
import Rainfall.Source.Exp
import qualified Text.Parsec            as P


parseDecl :: [At Token] -> Either P.ParseError (Decl RL)
parseDecl toks
 = P.runParser pDecl () "source" toks


parseTerm :: [At Token] -> Either P.ParseError (Term RL)
parseTerm toks
 = P.runParser pTermArg () "source" toks
