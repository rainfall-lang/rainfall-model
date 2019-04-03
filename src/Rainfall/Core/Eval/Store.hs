
module Rainfall.Core.Eval.Store where
import Rainfall.Core.Exp
import Data.Map                         (Map)
import qualified Data.Map.Strict        as Map


type Weight = Integer

type Store  = Map (Fact ()) Weight

data Factoid a
        = Factoid (Fact a) Weight
        deriving (Show, Eq, Ord)

pattern (:*) f w        = Factoid f w


-- | Delete all factoids whose weight is one from the store.
storePrune :: Store -> Store
storePrune ss
 = Map.filter (\w -> w /= 0) ss

