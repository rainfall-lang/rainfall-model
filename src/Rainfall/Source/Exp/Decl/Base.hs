
module Rainfall.Source.Exp.Decl.Base where
import Rainfall.Source.Exp.Type
import Rainfall.Source.Exp.Term


----------------------------------------------------------------------- Decl --
-- | A top-level declaration.
data Decl a
        = DeclFact
        { declName      :: Name
        , declFields    :: [(Name, Type a)] }

        | DeclRule
        { declAnnot     :: a
        , declRule      :: Rule a }

        | DeclScenario
        { declAnnot     :: a
        , declScenario  :: Scenario a }
        deriving Show


----------------------------------------------------------------------- Rule --
-- | A transition rule.
data Rule a
        = Rule
        { ruleName      :: Name         -- ^ Name of the rule.
        , ruleMatch     :: [Match a]    -- ^ Fact matches.
        , ruleBody      :: Term a       -- ^ Body of the rule to create facts.
        } deriving Show


-- | A fact match clause.
data Match a
        = MatchAnn    a (Match a)

        | Match
        { matchGather   :: Gather a     -- ^ Gather facts from the store.
        , matchSelect   :: Select a     -- ^ Select result from gathered facts.
        , matchConsume  :: Consume a    -- ^ Consume gathered facts.
        , matchGain     :: Gain a       -- ^ Authority to gain from raked fact.
        } deriving Show


-- | Specifies which facts to consider during a rake.
data Gather a
        = GatherAnn     a (Gather a)

        | GatherPat
        { gatherName    :: Name
        , gatherFields  :: [(Name, GatherPat a)]
        , gatherPred    :: Maybe (Term a) }
        deriving Show


-- | Pattern to select facts to gather.
data GatherPat a
        = GatherPatBind Name        -- ^ Bind the value of the field.
        | GatherPatEq   (Term a)    -- ^ Check the field equals the value.
        deriving Show


-- | Which fact to select from the gathered set.
data Select a
        = SelectAnn     a (Select a)
        | SelectAny                 -- ^ Select any fact that matches.
        | SelectFirst   (Term a)    -- ^ Select the first fact.
        | SelectLast    (Term a)    -- ^ Select the last fact.
        deriving Show


-- | Whether to consume the selected fact.
data Consume a
        = ConsumeAnn    a (Consume a)
        | ConsumeNone               -- ^ Match on facts without consumption.
        | ConsumeWeight (Term a)    -- ^ Consume the given weight of fact.
        deriving Show


-- | Whether to gain authority from the selected fact.
data Gain a
        = GainAnn       a (Gain a)
        | GainNone                  -- ^ Retain the same authority.
        | GainCheck     (Term a)    -- ^ Check for auth, but don't gain it.
        | GainTerm      (Term a)    -- ^ Gain the given authority.
        deriving Show


------------------------------------------------------------------- Scenario --
-- | A test scenario.
data Scenario a
        = Scenario
        { scenarioName          :: Name
        , scenarioActions       :: [Action a] }
        deriving Show


-- | A scenario action.
data Action a
        = ActionAdd
        { actionTerm            :: Term a }

        | ActionFire
        { actionFireAuth        :: Term a
        , actionFireRules       :: Term a }

        | ActionDump
        deriving Show

