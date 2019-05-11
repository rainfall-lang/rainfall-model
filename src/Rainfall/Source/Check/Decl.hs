
module Rainfall.Source.Check.Decl where
import Rainfall.Source.Check.Base
import Rainfall.Source.Check.Error      ()
import qualified Data.Map               as Map


------------------------------------------------------------------------------------------- Decl --
-- | Check a list of top level declarations.
checkDecls :: [Decl a] -> IO [Decl a]
checkDecls ds
 = do   let facts   = Map.fromList [(nFact, ntsField) | DeclFact nFact ntsField <- ds]
        mapM (checkDecl facts) ds


-- | Check a single declaration.
checkDecl :: Facts a -> Decl a -> IO (Decl a)
checkDecl facts dd
 = case dd of
        DeclFact{}       -> return dd
        DeclRule rule    -> DeclRule     <$> checkRule facts rule
        DeclScenario scn -> DeclScenario <$> checkScenario facts scn


------------------------------------------------------------------------------------------- Rule --
-- | Check a source rule.
--   Type errors are thrown as exceptions in the IO monad.
checkRule :: Facts a -> Rule a -> IO (Rule a)
checkRule _facts r@(Rule _nRule _hsMatch _mBody)
 = return r


--------------------------------------------------------------------------------------- Scenario --
checkScenario :: Facts a -> Scenario a -> IO (Scenario a)
checkScenario _facts s@(Scenario _name _actions)
 = return s