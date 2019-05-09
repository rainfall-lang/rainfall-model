
module Rainfall.Source.Transform.Lower where
import Rainfall.Core.Exp.Base
import qualified Rainfall.Source.Exp                    as E
import qualified Rainfall.Core.Exp                      as C
import qualified Control.Monad.Trans.State.Strict       as S
import Data.Maybe

------------------------------------------------------------------------------------------ Fresh --
type S a = S.State (String, Int) a

runState :: String -> S a -> a
runState prefix m
 = S.evalState m (prefix, 1)

fresh :: S Name
fresh
 = do   (prefix, n) <- S.get
        S.put (prefix, n + 1)
        return $ Name (prefix ++ show n)


------------------------------------------------------------------------------------------ Lower --
-- | Lower a list of source decls to core.
lowerDecls :: [E.Decl a] -> S [C.Rule a]
lowerDecls ds
 = fmap catMaybes $ mapM lowerDecl ds


-- | Lower a source decl to core.
lowerDecl :: E.Decl a -> S (Maybe (C.Rule a))
lowerDecl d
 = case d of
        E.DeclFact{}      -> pure Nothing
        E.DeclRule rule   -> Just <$> lowerRule rule


-- Lower a source rule to core.
lowerRule :: E.Rule a -> S (C.Rule a)
lowerRule (E.Rule nRule _ms _m)
 = pure $ C.Rule nRule [] C.MUnit

