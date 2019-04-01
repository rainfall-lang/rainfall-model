
module Rainfall.Core.Exp.Predicates where
import Rainfall.Core.Exp.Base
import Rainfall.Core.Exp.Patterns
import Rainfall.Core.Exp.Term
import Rainfall.Core.Exp.Rule
import qualified Data.List      as List


isVTrue :: Value a -> Bool
isVTrue (VBool True)    = True
isVTrue _               = False


-- | Check if we can see a fact with the given authority.
seesFact  :: Auth -> Fact a -> Bool
seesFact aHas (Fact n _env aBy aObs _nsRules)
 = not $ null $ List.intersect aHas (List.union aBy aObs)
