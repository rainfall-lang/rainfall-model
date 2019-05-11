
module Rainfall.Main.Config where


-- | Command line modes.
data Mode
        = ModeNone
        | ModeLex       FilePath
        | ModeParse     FilePath
        | ModeCheck     FilePath
        | ModeLower     FilePath
        | ModeRun       FilePath
        deriving Show


-- | Main command line config.
data Config
        = Config
        { configMode    :: Mode }
        deriving Show


-- | Default command line config.
configZero
        = Config
        { configMode    = ModeNone }

