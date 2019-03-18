
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
        { matchBind     :: Bind             -- ^ Binder for facts in the following clauses.
        , matchResult   :: Bind             -- ^ Binder for the result.
        , matchRake     :: Rake a           -- ^ Rake for the facts.
        , matchAcquire  :: Acquire a        -- ^ Authority to acquire from raked facts.
        } deriving Show


---------------------------------------------------------------------------------------------------
data Rake a
        = Rake
        { rakeGather    :: Gather a         -- ^ How to gather facts from the store.
        , rakeSelect    :: Select a         -- ^ How to select result from the gathered facts.
        , rakeConsume   :: Consume a        -- ^ How to consume the gathered facts.
        } deriving Show


-- | How to select facts for consideration.
data Gather a
        = GatherAnn    a (Gather a)

        -- | Terms must all produce true.
        | GatherWhen  Name [Term a]
        deriving Show


data Select a
        = SelectAnn     a (Select a)

        -- | Require there to be a single gathered fact.
        | SelectOne

        -- | Select any fact which matches, pseudo non-determinstically.
        | SelectAny

        -- | Select all facts that match, collecting them into a set.
        | SelectAll

        -- | Sort facts by the given term, and select the first that matches.
        | SelectFirst

        -- | Sort facts by the given term, and select the last that matches.
        | SelectLast
        deriving Show


data Consume a
        = ConsumeAnn    a (Consume a)

        -- | Return facts without consuming them.
        | ConsumeRet

        -- | Consume entire available quantity from each selected fact.
        | ConsumeCollect

        -- | Consume the given weight of facts.
        | ConsumeWeight (Term a)
        deriving Show


---------------------------------------------------------------------------------------------------
data Acquire a
        = AcquireAnn    a (Acquire a)
        | AcquireSame                      -- ^ Retain the same authority.
        | AcquireTerm   (Term a)           -- ^ Acquire the given authority.
        deriving Show

