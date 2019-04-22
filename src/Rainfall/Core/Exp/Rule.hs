
module Rainfall.Core.Exp.Rule where
import Rainfall.Core.Exp.Base
import Rainfall.Core.Exp.Term


---------------------------------------------------------------------------------------------------
data Rule a
        = Rule
        { ruleName      :: Name         -- ^ Name of the rule.
        , ruleMatch     :: [Match a]    -- ^ Matches for the rule.
        , ruleBody      :: Term a       -- ^ Body of the rule.
        } deriving Show


---------------------------------------------------------------------------------------------------
data Match a
        = MatchAnn    a (Match a)

        | Match
        { matchBind     :: Bind         -- ^ Binder for facts in the following clauses.
        , matchGather   :: Gather a     -- ^ How to gather facts from the store.
        , matchSelect   :: Select a     -- ^ How to select result from the gathered facts.
        , matchConsume  :: Consume a    -- ^ How to consume the gathered facts.
        , matchGain     :: Gain a       -- ^ Authority to gain from raked fact.
        } deriving Show


-- | Specifies which facts to consider during a rake.
data Gather a
        = GatherAnn     a (Gather a)
        | GatherWhere   Name [Term a]   -- ^ Gather facts where the predicates are all true.
        deriving Show


-- | How to select a single fact from the gathered set.
data Select a
        = SelectAnn     a (Select a)
        | SelectAny                     -- ^ Select any fact that matches.
        | SelectFirst   (Term a)        -- ^ Select the first fact, ordered by this term.
        | SelectLast    (Term a)        -- ^ Select the last fact, ordered by this term
        deriving Show


-- | Whether to consume the selected fact.
data Consume a
        = ConsumeAnn    a (Consume a)
        | ConsumeNone                   -- ^ Match on facts without consuming them.
        | ConsumeWeight (Term a)        -- ^ Consume the given weight of fact.
        deriving Show


-- | Whether to gain authority from the selected fact.
data Gain a
        = GainAnn       a (Gain a)
        | GainNone                      -- ^ Retain the same authority.
        | GainTerm      (Term a)        -- ^ Gain the given authority.
        deriving Show

