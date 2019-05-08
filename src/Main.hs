
module Main where

import qualified Rainfall.Main.Args                     as Main
import qualified Rainfall.Main.Config                   as Main

import qualified Rainfall.Source.Codec.Text.Token       as Token
import qualified Rainfall.Source.Codec.Text.Lexer       as Lexer

import qualified System.Environment                     as System
import qualified System.Exit                            as System


------------------------------------------------------------------------------------------- Main --
main :: IO ()
main
 = do   args    <- System.getArgs
        config  <- Main.parseArgs args Main.configZero
        case Main.configMode config of
         Main.ModeNone
          -> do putStrLn $ Main.usage
                System.exitSuccess

         Main.ModeLex filePath -> runLex config filePath


-------------------------------------------------------------------------------------------- Lex --
runLex _config filePath
 = do   str     <- readFile filePath

        case Lexer.scanSource filePath str of
         (toks, _, [])
          -> putStr $ unlines $ map show toks

         (_, Token.Location l c, _)
          -> do putStrLn $ filePath ++ ":" ++ show (l + 1) ++ ":" ++ show (c + 1)
                         ++ " lexical error"
                System.exitFailure

