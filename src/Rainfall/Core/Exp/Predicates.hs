
module Rainfall.Core.Exp.Predicates where
import Rainfall.Core.Exp.Base
import Rainfall.Core.Exp.Patterns
import Rainfall.Core.Exp.Term
import qualified Data.Set       as Set

isVTrue :: Value a -> Bool

isVTrue (VBool True)    = True
isVTrue _               = False


-- | Check if we can see a fact with the given authority.
canSeeFact  :: Auth -> Fact a -> Bool
canSeeFact aSub (Fact _n _env aBy aObs _nsRules)
 = not $ null $ Set.intersection aSub (Set.union aBy aObs)


-- | Check if the 'by' authority of a fact is a subset of the given authority.
authCoversFact :: Auth -> Fact a -> Bool
authCoversFact auth fact
 = Set.isSubsetOf (factBy fact) auth
