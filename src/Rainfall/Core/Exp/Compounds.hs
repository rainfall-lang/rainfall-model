
module Rainfall.Core.Exp.Compounds where
import Rainfall.Core.Exp.Base
import Rainfall.Core.Exp.Term


-- | Bind a single value into an environment.
envBind :: Bind -> Value a -> Env a -> Env a
envBind BindNone _ env          = env
envBind (BindName n) v env      = (n, v) : env

