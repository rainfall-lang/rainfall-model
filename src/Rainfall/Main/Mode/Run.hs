
module Rainfall.Main.Mode.Run where
import qualified Rainfall.Main.Config                   as Main
import qualified Rainfall.Source.Codec.Text.Parser      as Parser
import qualified Rainfall.Core.Exp                      as C
import qualified Rainfall.Core.Eval                     as C
import qualified Rainfall.Core.Codec.Text.Pretty        as C

import Data.Map                                         (Map)
import qualified Text.PrettyPrint.Leijen                as P
import qualified Control.Monad.Trans.State.Strict       as S
import qualified Control.Monad.IO.Class                 as S
import qualified Data.Map                               as Map
import qualified Data.Set                               as Set


------------------------------------------------------------------------------------------ World --
type S a
        = S.StateT World IO a

data World
        = World
        { worldStore    :: C.Store
        , worldRules    :: Map C.Name (C.Rule Parser.RL) }
        deriving Show


--------------------------------------------------------------------------------------- Scenario --
runScenario
        :: Main.Config
        -> [C.Rule Parser.RL]
        -> C.Scenario Parser.RL
        -> IO ()

runScenario config rules (C.Scenario _name actions)
 = do
        let world
                = World
                { worldStore    = C.storeEmpty
                , worldRules    = Map.fromList [ (C.ruleName r, r) | r <- rules ] }

        flip S.evalStateT world
         $ mapM_ (runAction config) actions


----------------------------------------------------------------------------------------- Action --
-- | Run a single scenario action.
runAction
        :: Main.Config
        -> C.Action Parser.RL -> S ()

runAction _config (C.ActionAdd mFoids)
 = do   let vFoids      = C.evalTerm (C.Env []) mFoids
        let Just foids  = C.takeFactoidsOfValue vFoids
        S.modify $ \s -> s {
                worldStore = Map.unionWith (+) foids (worldStore s) }

runAction _config (C.ActionFire mSub mRules)
 = do   let Just aSub   = C.takeAuthOfValue  $ C.evalTerm (C.Env []) mSub
        let Just rs     = C.takeRulesOfValue $ C.evalTerm (C.Env []) mRules
        mapM_ (fireRuleS aSub) $ Set.toList rs

runAction _config C.ActionDump
 = do   store   <- S.gets worldStore
        S.liftIO $ putStrLn $ (P.displayS $ renderMax $ C.ppStore store) ""


------------------------------------------------------------------------------------------- Fire --
-- | Try and fire the given rule, printing the result to stdout.
fireRuleS :: C.Auth -> C.Name -> S ()
fireRuleS aSub nRule
 = do   store   <- S.gets worldStore
        rules   <- S.gets worldRules
        case Map.lookup nRule rules of
         Nothing
          -> do S.liftIO $ putStrLn $ "! no such rule " ++ show nRule

         Just rule
          -> do mResult <- S.liftIO $ fireRuleIO aSub rule store
                case mResult of
                 Nothing -> return ()
                 Just (_trans, store')
                  -> do S.modify' $ \s -> s { worldStore = store' }
                        return ()


-- | Try to fire the given rule, printing the result to stdout.
fireRuleIO
        :: C.Auth
        -> C.Rule Parser.RL
        -> C.Store -> IO (Maybe (C.Transaction, C.Store))

fireRuleIO auth rule store
 = do   let C.Name sName = C.ruleName rule
        putStrLn $ "* Fire: " ++ sName

        case C.applyFire auth store rule of
         []
          -> do putStrLn $ "* Fizz: " ++ sName
                return Nothing

         [(trans, store')]
          -> do let dsSpent = Map.toList $ C.transactionSpent trans
                let dsNew   = Map.toList $ C.transactionNew   trans
                putStrLn $ (P.displayS $ renderMax $ C.ppFiring dsSpent dsNew store') ""
                return $ Just (trans, store')

         _ -> do
                putStrLn "* Many"
                return Nothing

renderMax = P.renderPretty 1.0 100