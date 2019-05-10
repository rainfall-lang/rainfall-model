
module Main where

import qualified Rainfall.Main.Args                     as Main
import qualified Rainfall.Main.Config                   as Main
import qualified Rainfall.Main.Mode.Run                 as Main

import qualified Rainfall.Source.Exp                    as S
import qualified Rainfall.Source.Codec.Text.Token       as Token
import qualified Rainfall.Source.Codec.Text.Lexer       as Lexer
import qualified Rainfall.Source.Codec.Text.Parser      as Parser
import qualified Rainfall.Source.Transform.Lower        as Lower

import qualified Rainfall.Core.Exp                      as C

import qualified System.Environment                     as System
import qualified System.Exit                            as System

import qualified Text.Show.Pretty                       as Pretty


------------------------------------------------------------------------------------------- Main --
main :: IO ()
main
 = do   args    <- System.getArgs
        config  <- Main.parseArgs args Main.configZero
        case Main.configMode config of
         Main.ModeLex   filePath -> mainLex   config filePath
         Main.ModeParse filePath -> mainParse config filePath
         Main.ModeLower filePath -> mainLower config filePath
         Main.ModeRun   filePath -> mainRun   config filePath

         Main.ModeNone
          -> do putStrLn $ Main.usage
                System.exitSuccess


-------------------------------------------------------------------------------------------- Lex --
-- | Perform lexical analysis on a source file,
--   then print the tokens to console.
runLex :: Main.Config -> FilePath -> IO [Token.At Token.Token]
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
-- | Parse a source file and print the AST to console.
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
        putStrLn $ Pretty.ppShow ds


------------------------------------------------------------------------------------------ Lower --
-- | Parse a source file, lower it to core, then print the core AST to console.
runLower :: Main.Config -> FilePath -> IO [C.Decl Parser.RL]
runLower config filePath
 = do   dsSource   <- runParse config filePath
        let dsCore =  Lower.runState "w" $ Lower.lowerDecls dsSource
        return dsCore

mainLower config filePath
 = do   rs      <- runLower config filePath
        putStrLn $ Pretty.ppShow rs


-------------------------------------------------------------------------------------------- Run --
-- | Load a source file and run the scenario tests.
runRun :: Main.Config -> FilePath -> IO ()
runRun config filePath
 = do   dsCore  <- runLower config filePath

        let rules       = [rule | C.DeclRule     rule <- dsCore]
        let scenarios   = [scen | C.DeclScenario scen <- dsCore]

        mapM_ (Main.runScenario config rules) scenarios

mainRun config filePath
 = runRun config filePath


