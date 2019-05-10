
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


-- | Add new factoids to a store.
storeUp :: Store -> Factoids -> Store
storeUp store factoids
 = Map.unionWith (+) store factoids


-- | Remove factoids from the store.
storeDown :: Store -> Factoids -> Maybe Store
storeDown store factoids
 | all (supports store) $ Map.toList factoids
 = Just $ Map.filter (\w -> w > 0)
        $ Map.unionWith (-) store factoids

 | otherwise
 = Nothing


-- | Check that the store supports (includes) the given factoids.
supports :: Store -> Factoid -> Bool
supports store (fact, weight)
 = case Map.lookup fact store of
        Nothing         -> weight == 0
        Just wAvail     -> wAvail >= weight
