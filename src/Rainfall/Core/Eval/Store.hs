
module Rainfall.Core.Eval.Store where
import Rainfall.Core.Exp
import Data.Map                 (Map)


type Weight = Integer

type Store  = Map (Fact ()) Weight

data Factoid a
        = Factoid (Fact a) Weight
        deriving (Show, Eq, Ord)

pattern (:*) f w        = Factoid f w


