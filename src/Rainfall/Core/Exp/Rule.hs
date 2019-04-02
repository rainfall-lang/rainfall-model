
module Rainfall.Core.Exp.Rule where
import Rainfall.Core.Exp.Base
import Rainfall.Core.Exp.Term


---------------------------------------------------------------------------------------------------
data Rule a
        = Rule
        { ruleName      :: Name                 -- ^ Name of the rule.
        , ruleMatch     :: [Match a]            -- ^ Matches for the rule.
        , ruleBody      :: Term a               -- ^ Body of the rule.
        } deriving Show


---------------------------------------------------------------------------------------------------
data Match a
        = MatchAnn    a (Match a)

        | Match
        { matchRake     :: Rake a           -- ^ Rake for the facts.
        , matchAcquire  :: Acquire a        -- ^ Authority to acquire from raked fact.
        } deriving Show


---------------------------------------------------------------------------------------------------
-- | Specifies how to retrieve facts from the store.
data Rake a
        = Rake
        { rakeBind      :: Bind             -- ^ Binder for facts in the following clauses.
        , rakeGather    :: Gather a         -- ^ How to gather facts from the store.
        , rakeSelect    :: Select a         -- ^ How to select result from the gathered facts.
        , rakeConsume   :: Consume a        -- ^ How to consume the gathered facts.
        } deriving Show


-- | Specifies which facts to consider during a rake.
data Gather a
        = GatherAnn    a (Gather a)

        -- | Terms must all produce true.
        | GatherWhen  Name [Term a]
        deriving Show


-- | Specifies how to select facts from the gathered set.
data Select a
        = SelectAnn     a (Select a)

        -- | Require there to be a single gathered fact.
        | SelectOne

        -- | Select any fact which matches, pseudo non-determinstically.
        | SelectAny

        -- | Sort facts by the given term, and select the first that matches.
        | SelectFirst   (Term a)

        -- | Sort facts by the given term, and select the last that matches.
        | SelectLast    (Term a)
        deriving Show


-- | Specifies how to treat selected facts.
data Consume a
        = ConsumeAnn    a (Consume a)

        -- | Return facts without consuming them.
        | ConsumeRetain

        -- | Consume the given weight of the fact.
        | ConsumeWeight (Term a)
        deriving Show


---------------------------------------------------------------------------------------------------
data Acquire a
        = AcquireAnn    a (Acquire a)
        | AcquireSame                      -- ^ Retain the same authority.
        | AcquireTerm   (Term a)           -- ^ Acquire the given authority.
        deriving Show

