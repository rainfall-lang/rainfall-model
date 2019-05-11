
module Rainfall.Source.Check.Base
        ( module Rainfall.Source.Check.Error
        , module Rainfall.Source.Exp
        , Facts
        , Context (..))
where
import Rainfall.Source.Check.Error
import Rainfall.Source.Exp


-- | Map of fact names to their payload types.
type Facts a = Map Name [(Name, Type a)]


data Context a
        = Context
        { -- | Definitions of top-level facts.
          contextFacts  :: Facts a

          -- | Local environment when checking a rule.
        , contextLocal  :: [(Name, Type a)]
        }
        deriving (Show)
