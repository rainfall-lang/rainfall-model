
module Main where

import qualified Rainfall.Main.Args                     as Main
import qualified Rainfall.Main.Config                   as Main
import qualified Rainfall.Main.Mode.Run                 as Main

import qualified Rainfall.Source.Exp                    as S
import qualified Rainfall.Source.Codec.Text.Token       as Token
import qualified Rainfall.Source.Codec.Text.Lexer       as Lexer
import qualified Rainfall.Source.Codec.Text.Parser      as Parser
import qualified Rainfall.Source.Check                  as Check
import qualified Rainfall.Source.Transform.Lower        as Lower

import qualified Rainfall.Core.Exp                      as C

import qualified System.Environment                     as System
import qualified System.Exit                            as System

import qualified Text.Show.Pretty                       as Pretty
import qualified Text.Parsec.Error                      as Parsec
import qualified Text.Parsec.Pos                        as Parsec

----------------------------------------------------------------------- Main --
main :: IO ()
main
 = do   args    <- System.getArgs
        config  <- Main.parseArgs args Main.configZero
        case Main.configMode config of
         Main.ModeLex   filePath -> mainLex   config filePath
         Main.ModeParse filePath -> mainParse config filePath
         Main.ModeLower filePath -> mainLower config filePath
         Main.ModeRun   filePath -> mainRun   config filePath
         Main.ModeCheck filePath -> mainCheck config filePath

         Main.ModeNone
          -> do putStrLn $ Main.usage
                System.exitSuccess


------------------------------------------------------------------------ Lex --
-- | Perform lexical analysis on a source file,
--   then print the tokens to console.
runLex :: Main.Config -> FilePath -> IO [Token.At Token.Token]
runLex _config filePath
 = do   str     <- readFile filePath

        case Lexer.scanSource filePath str of
         (toks, _, [])
          -> return toks

         (_, Token.Location l c, _)
          -> do putStrLn
                 $ filePath ++ ":" ++ show (l + 1) ++ ":" ++ show (c + 1)
                            ++ " lexical error"
                System.exitFailure

mainLex config filePath
 = do   toks    <- runLex config filePath
        putStr $ unlines $ map show toks


---------------------------------------------------------------------- Parse --
-- | Parse a source file and print the AST to console.
runParse :: Main.Config -> FilePath -> IO [S.Decl Parser.RL]
runParse config filePath
 = do   -- Run lexical analysis on the source file.
        toks     <- runLex config filePath

        -- Strip comments before parsing.
        let toks' = [ ak | ak@(Token.At _ k) <- toks
                         , not $ Token.isKCOMMENT k ]

        -- Parse declarations from the file.
        case Parser.parseDecls toks' of
         Right ds -> return ds
         Left err
          -> do let pos = Parsec.errorPos err
                putStrLn $ filePath
                 ++ ":" ++ show (Parsec.sourceLine pos + 1)
                 ++ ":" ++ show (Parsec.sourceColumn pos + 1)
                 ++ " parse error"
                System.exitFailure

mainParse config filePath
 = do   ds       <- runParse config filePath
        putStrLn $ Pretty.ppShow ds


---------------------------------------------------------------------- Check --
-- | Parse and check a source file,
--   returning a list of checked top-level declarations.
runCheck :: Main.Config -> FilePath -> IO [S.Decl Parser.RL]
runCheck config filePath
 = do   dsSource  <- runParse config filePath
        dsChecked <- Check.checkDecls dsSource
        return dsChecked

mainCheck config filePath
 = do   _ds      <- runCheck config filePath
        return ()


---------------------------------------------------------------------- Lower --
-- | Parse a source file, lower it to core, then print the core AST to console.
runLower :: Main.Config -> FilePath -> IO [C.Decl Parser.RL]
runLower config filePath
 = do   dsSource   <- runCheck config filePath
        let dsCore =  Lower.runState "w" $ Lower.lowerDecls dsSource
        return dsCore

mainLower config filePath
 = do   rs      <- runLower config filePath
        putStrLn $ Pretty.ppShow rs


------------------------------------------------------------------------ Run --
-- | Load a source file and run the scenario tests.
runRun :: Main.Config -> FilePath -> IO ()
runRun config filePath
 = do   dsCore  <- runLower config filePath

        let rules       = [rule | C.DeclRule     rule <- dsCore]
        let scenarios   = [scen | C.DeclScenario scen <- dsCore]

        mapM_ (Main.runScenario config rules) scenarios

mainRun config filePath
 = runRun config filePath


