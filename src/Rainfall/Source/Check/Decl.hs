
module Rainfall.Source.Check.Decl where
import Rainfall.Source.Check.Term
import Rainfall.Source.Check.Base
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
checkRule facts (Rule nRule hsMatch mBody)
 = do   -- Initial context.
        let ctx     = Context facts []

        -- Check all the matches, producing an output context with pattern bindings.
        (ctx', hsMatch') <- checkMatches ctx hsMatch

        -- Check the body in the new context.
        mBody'  <- checkTerm ctx' mBody

        return (Rule nRule hsMatch' mBody')


------------------------------------------------------------------------------------------ Match --
-- | Check a sequence of matches,
--   where variables bound in earlier ones are in scope in later ones.
checkMatches :: Context a -> [Match a] -> IO (Context a, [Match a])
checkMatches ctx []
 = return (ctx, [])

checkMatches ctx (h: hs)
 = do   (ctx', h')   <- checkMatch   ctx  h
        (ctx'', hs') <- checkMatches ctx' hs
        return (ctx'', h' : hs')


-- | Check a single match clause.
checkMatch :: Context a -> Match a -> IO (Context a, Match a)
checkMatch ctx (MatchAnn a h)
 = do   (ctx', h') <- checkMatch ctx h
        return $ (ctx', MatchAnn a h')

checkMatch ctx (Match mBind gather select consume gain)
 = do
        return (ctx, Match mBind gather select consume gain)


--------------------------------------------------------------------------------------- Scenario --
checkScenario :: Facts a -> Scenario a -> IO (Scenario a)
checkScenario _facts s@(Scenario _name _actions)
 = return s