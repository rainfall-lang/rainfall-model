
module Main where

import qualified Rainfall.Main.Args                     as Main
import qualified Rainfall.Main.Config                   as Main

import qualified Rainfall.Source.Codec.Text.Token       as Token
import qualified Rainfall.Source.Codec.Text.Lexer       as Lexer
import qualified Rainfall.Source.Codec.Text.Parser      as Parser
import qualified Rainfall.Source.Exp                    as S

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
runParse :: Main.Config -> FilePath -> IO [S.Decl Parser.RL]
runParse config filePath
 = do   toks    <- runLex config filePath
        case Parser.parseDecls toks of
         Right ds -> return ds
         Left err
          -> do putStrLn $ show err
                System.exitFailure

mainParse config filePath
 = do   ds       <- runParse config filePath
        print ds


