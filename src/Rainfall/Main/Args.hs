
module Rainfall.Main.Args where
import Rainfall.Main.Config
import qualified System.Exit    as System


parseArgs :: [String] -> Config -> IO Config
parseArgs ("-lex" : filePath : rest) config
 = parseArgs rest
 $ config { configMode = ModeLex filePath }

parseArgs ("-parse" : filePath : rest) config
 = parseArgs rest
 $ config { configMode = ModeParse filePath }

parseArgs [] config
 = return config

parseArgs _args _
 = do   putStrLn usage
        System.exitFailure

usage
 = unlines
 [ "rainfall -lex   FILE.rain        lex a file and print tokens"
 , "rainfall -parse FILE.rain        parse a file and print tokens"]
