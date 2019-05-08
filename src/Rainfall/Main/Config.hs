
module Rainfall.Main.Config where


data Mode
        = ModeNone
        | ModeLex FilePath
        deriving Show


data Config
        = Config
        { configMode    :: Mode }
        deriving Show

configZero
        = Config
        { configMode    = ModeNone }