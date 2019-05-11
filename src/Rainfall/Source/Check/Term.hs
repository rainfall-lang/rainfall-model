
module Rainfall.Source.Check.Term where
import Rainfall.Source.Check.Base


------------------------------------------------------------------------------------------- Term --
-- | Type check a single term.
checkTerm :: Context a -> Term a -> IO (Term a, Type a)
checkTerm _ctx m
 = return (m, TUnit)

