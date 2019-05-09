
module Rainfall.Source.Codec.Text.Parser
        ( RL
        , parseDecls, parseDecl
        , parseTerm)
where
import Rainfall.Source.Codec.Text.Parser.Decl
import Rainfall.Source.Codec.Text.Parser.Term
import Rainfall.Source.Codec.Text.Parser.Base
import Rainfall.Source.Codec.Text.Token
import Rainfall.Source.Exp
import qualified Text.Parsec                    as P
import qualified Text.Lexer.Inchworm.Source     as IW


parseDecl :: [At Token] -> Either P.ParseError (Decl RL)
parseDecl toks
 = P.runParser pDecl () "source" toks


parseDecls :: [At Token] -> Either P.ParseError [Decl RL]
parseDecls toks
 = P.runParser
        (do ds <- pDecls; pTok KEND; return ds)
        () "source" (toks ++ [At rZero KEND])
 where  lZero   = IW.Location 0 0
        rZero   = IW.Range lZero lZero

parseTerm :: [At Token] -> Either P.ParseError (Term RL)
parseTerm toks
 = P.runParser pTermArg () "source" toks
