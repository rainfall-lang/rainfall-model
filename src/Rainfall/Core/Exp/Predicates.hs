
module Rainfall.Core.Exp.Predicates where
import Rainfall.Core.Exp.Base
import Rainfall.Core.Exp.Patterns
import Rainfall.Core.Exp.Term
import Rainfall.Core.Exp.Rule
import qualified Data.List      as List
import qualified Data.Set       as Set

isVTrue :: Value a -> Bool
isVTrue (VBool True)    = True
isVTrue _               = False


-- | Check if we can see a fact with the given authority.
canSeeFact  :: Auth -> Fact a -> Bool
canSeeFact aHas (Fact n _env aBy aObs _nsRules)
 = not $ null $ List.intersect aHas (List.union aBy aObs)


-- | Check if we can consume a fact with the given rule and authority.
canConsumeFact :: Name -> Auth -> Fact a -> Bool
canConsumeFact nRule aHas (Fact n _env aBy aObs nsRules)
 =  elem nRule nsRules
 && Set.isSubsetOf (Set.fromList aBy) (Set.fromList aHas)

