
module Rainfall.Core.Eval.Store where
import Rainfall.Core.Exp
import Data.Map                         (Map)
import qualified Data.Map.Strict        as Map

type Store = Map Fact Weight

pattern (:*) f w = (f, w)

-- | An empty store.
storeEmpty :: Store
storeEmpty
 = Map.empty

-- | Delete all factoids whose weight is one from the store.
storePrune :: Store -> Store
storePrune ss
 = Map.filter (\w -> w /= 0) ss

