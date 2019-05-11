
module Rainfall.Source.Check.Base
        ( module Rainfall.Source.Check.Error
        , module Rainfall.Source.Exp
        , Facts
        , Context (..)
        , checkEq
        , RL
        , nope)
where
import Rainfall.Source.Check.Error
import Rainfall.Source.Exp
import qualified Rainfall.Source.Codec.Text.Token       as Token
import qualified System.Exit                            as System
import qualified Data.Map.Strict                        as Map

---------------------------------------------------------------------------------------- Context --
-- | Map of fact names to their payload types.
type Facts a = Map Name [(Name, Type a)]

-- | Stack mapping local variable names to their types.
type Local a = [(Name, Type a)]

-- | Type checker context.
data Context a
        = Context
        { -- | Definitions of top-level facts.
          contextFacts  :: Facts a

          -- | Local environment when checking a rule.
        , contextLocal  :: Local a
        } deriving (Show)


type RL = Token.Range Token.Location


--------------------------------------------------------------------------------------------- Eq --
-- | Check whether the given types are equivalent.
checkEq :: Type a -> Type a -> Bool

checkEq (TAnn _a t1) t2         = checkEq t1 t2
checkEq t1 (TAnn _a t2)         = checkEq t1 t2

checkEq (TPrm n1) (TPrm n2)     = n1 == n2
checkEq (TCon n1) (TCon n2)     = n1 == n2

checkEq TBot TBot               = True

checkEq (TFun t11 t12) (TFun t21 t22)
 = checkEq t11 t21 && checkEq t12 t22

checkEq (TRcd ns1 ts1) (TRcd ns2 ts2)
 |  length ns1 == length ns2
 ,  length ns1 == length ts1
 ,  length ns2 == length ts2
 = let  mp1     = Map.fromList $ zip ns1 ts1
        mp2     = Map.fromList $ zip ns2 ts2
   in   (Map.keys mp1 == Map.keys mp2)
     && and (zipWith checkEq (Map.elems mp1) (Map.elems mp2))

checkEq (TSet  t1) (TSet  t2)   = checkEq t1 t2
checkEq (TSets t1) (TSets t2)   = checkEq t1 t2

checkEq (TFact t1) (TFact t2)   = checkEq t1 t2
checkEq TFACT TFACT             = True

checkEq _ _                     = False


------------------------------------------------------------------------------------------ Error --
nope :: RL -> [String] -> IO a
nope a str
 = do   putStrLn "type error"
        putStr $ " " ++ sloc a ++ " " ++ unlines str
        System.exitFailure

 where  sloc  (Token.Range (Token.Location l c) _)
         = show (l + 1) ++ ":" ++ show (c + 1)
