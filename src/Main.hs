
module Main where

import qualified Rainfall.Main.Args                     as Main
import qualified Rainfall.Main.Config                   as Main

import qualified Rainfall.Source.Codec.Text.Token       as Token
import qualified Rainfall.Source.Codec.Text.Lexer       as Lexer
import qualified Rainfall.Source.Codec.Text.Parser      as Parser

import qualified System.Environment                     as System
import qualified System.Exit                            as System


------------------------------------------------------------------------------------------- Main --
main :: IO ()
main
 = do   args    <- System.getArgs
        config  <- Main.parseArgs args Main.configZero
        case Main.configMode config of
         Main.ModeLex filePath          -> mainLex config filePath
         Main.ModeParse filePath        -> mainParse config filePath

         Main.ModeNone
          -> do putStrLn $ Main.usage
                System.exitSuccess



-------------------------------------------------------------------------------------------- Lex --
runLex _config filePath
 = do   str     <- readFile filePath

        case Lexer.scanSource filePath str of
         (toks, _, [])
          -> return toks

         (_, Token.Location l c, _)
          -> do putStrLn $ filePath ++ ":" ++ show (l + 1) ++ ":" ++ show (c + 1)
                         ++ " lexical error"
                System.exitFailure


mainLex config filePath
 = do   toks    <- runLex config filePath
        putStr $ unlines $ map show toks


------------------------------------------------------------------------------------------ Parse --
runParse config filePath
 = do   toks    <- runLex config filePath
        let e    = Parser.parseDecl toks
        return e



mainParse config filePath
 = do   e       <- runParse config filePath
        print e


