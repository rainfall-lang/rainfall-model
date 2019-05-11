
module Rainfall.Source.Check.Base
        ( module Rainfall.Source.Exp
        , Facts)
where
import Rainfall.Source.Exp

-- | Map of fact names to their payload types.
type Facts a = Map Name [(Name, Type a)]


