
module Rainfall.EDSL
        ( module Rainfall.Core.Exp
        , rule
        , match'any, match'when
        , when
        , anyof, firstof, lastof
        , none, weight, consume
        , same, check, gain
        , unit, bool, sym, nat, text, party, auth, rules
        , (!), pattern (:=)
        , auths

        , say
        , bool'eq
        , nat'add, nat'sub, nat'eq, nat'le, nat'ge
        , text'eq
        , symbol'eq
        , party'eq
        , auth'one, auth'union, auth'unions, auth'parties

        , runScenario
        , printStoreS
--        , sayS, sayS'
        , fireS, fireIO)
where
import Rainfall.Core.Exp
import Rainfall.Core.Eval
import Rainfall.Core.Codec.Text.Pretty
import Data.Map                                         (Map)
import qualified Control.Monad.Trans.State.Strict       as S
import qualified Control.Monad.IO.Class                 as S
import qualified Text.PrettyPrint.Leijen                as P
import qualified Data.Set                               as Set
import qualified Data.Map                               as Map


-- Rule -------------------------------------------------------------------------------------------
rule n ms mBody         = Rule  n ms mBody
match'any  x n g c i    = Match x (when n []) g c i
match'when x n ms g c i = Match x (when n ms) g c i

when  n ms              = GatherWhere n ms

anyof                   = SelectAny
firstof                 = SelectFirst
lastof                  = SelectLast

none                    = ConsumeNone
weight m                = ConsumeWeight m
consume n               = ConsumeWeight (MNat n)

same                    = GainNone
check m                 = GainCheck m
gain  m                 = GainTerm m


-- Term -------------------------------------------------------------------------------------------
unit                    = MUnit
bool  b                 = MBool  b
nat   n                 = MNat   n
text  t                 = MText  t
sym   s                 = MSym   s
party n                 = MParty n
auth  ns                = MSet $ map party ns
rules ns                = MSet $ map sym ns

(!) m n                 = MPrj m n
pattern (:=) a b        = (a, b)
infixl 0 :=

auths ns                = Set.fromList ns

-- Prim -------------------------------------------------------------------------------------------
say nFact nmsFields nmsMeta
 = let  (nsFields, vsFields)    = unzip nmsFields
        (nsMeta,   vsMeta)      = unzip nmsMeta
   in   MSay nFact (MRcd nsFields vsFields) (MRcd nsMeta vsMeta)

bool'eq mx my           = MPrm "bool'eq"    [mx, my]

nat'add nx ny           = MPrm "nat'add"    [nx, ny]
nat'sub nx ny           = MPrm "nat'sub"    [nx, ny]
nat'eq  nx ny           = MPrm "nat'eq"     [nx, ny]
nat'le  nx ny           = MPrm "nat'le"     [nx, ny]
nat'ge  nx ny           = MPrm "nat'ge"     [nx, ny]

text'eq tx ty           = MPrm "text'eq"    [tx, ty]

symbol'eq mx my         = MPrm "symbol'eq"  [mx, my]

party'eq  mx my         = MPrm "party'eq"   [mx, my]

auth'one   mp           = MPrm "auth'one"   [mp]
auth'union ma mb        = MPrm "auth'union" [ma, mb]
auth'unions ms          = foldr auth'union auth'none ms
auth'none               = MSet []
auth'parties ms         = foldr auth'union auth'none $ map auth'one ms


------------------------------------------------------------------------------------------ World --
data World
        = World
        { worldParties  :: [Name]
        , worldStore    :: Store
        , worldRules    :: Map Name (Rule ()) }
        deriving Show



--------------------------------------------------------------------------------------- Scenario --
type Scenario a = S.StateT World IO a


runScenario :: [Name] -> [Rule ()] -> Scenario a -> IO a
runScenario nsParty rules scenario
 = do   S.evalStateT scenario
         $ World
         { worldParties = nsParty
         , worldStore   = storeEmpty
         , worldRules   = Map.fromList [ (ruleName r, r) | r <- rules] }


---- | Add a fact to the store with authority of a single party.
--sayS :: Name -> Name -> [(Name, Term ())] -> [(Name, Term ())] -> Scenario ()
--sayS _nParty nFact nmsFields nmsMeta
-- = do
--        let (_, [(fact, num)])
--                = evalTerm []
--                $ say nFact nmsFields nmsMeta
--
--        -- TODO: check by is covered by nParty
--        store <- S.gets worldStore
--        S.modify' $ \s -> s { worldStore = Map.insertWith (+) fact num store }


---- | Wrapper for `sayS` to help fill in some of the fields.
--sayS'   :: Name                 -- ^ Name of submitting party.
--        -> [Name]               -- ^ Names of observing parties.
--        -> Name                 -- ^ Name of fact to add.
--        -> [(Name, Term ())]    -- ^ Terms for fields.
--        -> [Name]               -- ^ Names of useable rules.
--        -> Weight               -- ^ Weight of fact.
--        -> Scenario ()
--
--sayS' nSub nsObs nFact nvsEnv nsUse weight
-- = sayS nSub nFact
--        nvsEnv
--        [ "by" := auth [nSub], "obs" := auth nsObs, "use" := rules nsUse, "num" := nat weight ]


-- | Try to fire a single rule in the scenario monad,
--   using the first available firing.
fireS :: [Name] -> Name -> Scenario ()
fireS nsSub nRule
 = do   store   <- S.gets worldStore
        rules   <- S.gets worldRules
        case Map.lookup nRule rules of
         Nothing
          -> do S.liftIO $ putStrLn $ "! no such rule " ++ show nRule

         Just rule
          -> do mResult <- S.liftIO $ fireIO (auths nsSub) rule store
                case mResult of
                 Nothing        -> return ()
                 Just (_trans, store')
                  -> do S.modify' $ \s -> s { worldStore = store'}
                        return ()

printStoreS :: Scenario ()
printStoreS
 = do   store   <- S.gets worldStore
        S.liftIO $ putStrLn $ (P.displayS $ renderMax $ ppStore store) ""


--------------------------------------------------------------------------------------------- IO --
-- | Try to fire the given rule, succeding only if there is a single available firing.
fireIO :: Auth -> Rule () -> Store -> IO (Maybe (Transaction, Store))
fireIO auth rule store
 = do   let Name sName = ruleName rule
        putStrLn $ "* Rule " ++ sName
        case applyFire auth store rule of
         []
          -> do putStrLn "* Fizz"
                return Nothing

         [(trans, store')]
          -> do let dsSpent = Map.toList $ transactionSpent trans
                let dsNew   = Map.toList $ transactionNew   trans
                putStrLn $ (P.displayS $ renderMax $ ppFiring dsSpent dsNew store') ""
                return $ Just (trans, store')

         _ -> do
                putStrLn "* Many"
                return Nothing


renderMax = P.renderPretty 1.0 100