
module Rainfall.EDSL
        ( module Rainfall.Core.Exp
        , rule
        , match'any, match'when
        , when
        , anyof, firstof, lastof
        , none, weight, consume
        , same, gain
        , unit, bool, sym, nat, text, party, auth, rules
        , (!), pattern (:=)
        , auths

        , say
        , symbol'eq
        , party'eq
        , auth'one, auth'union
        , nat'add, nat'eq, nat'le, nat'ge
        , text'eq

        , runFire)
where
import Rainfall.Core.Exp
import Rainfall.Core.Eval
import Rainfall.Core.Codec.Text.Pretty
import Data.String
import qualified Text.PrettyPrint.Leijen        as P
import qualified Data.Set                       as Set

instance IsString (Term a) where
 fromString s = MVar s

instance IsString (Value a) where
 fromString s = VText s

instance IsString Bind where
 fromString s = BindName s


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
gain m                  = GainTerm m


-- Term -------------------------------------------------------------------------------------------
unit                    = MUnit
bool  b                 = MBool  b
sym   s                 = MSym   s
nat   n                 = MNat   n
text  t                 = MText  t
party n                 = MParty n
auth  ns                = MAuth  (Set.fromList ns)
rules ns                = MRules ns

(!) m n                 = MPrj m n
pattern (:=) a b        = (a, b)

auths ns                = Set.fromList ns

-- Prim -------------------------------------------------------------------------------------------
say nFact nmsFields nmsMeta
 = let  (nsFields, vsFields)    = unzip nmsFields
        (nsMeta,   vsMeta)      = unzip nmsMeta
   in   MSay nFact (MRcd nsFields vsFields) (MRcd nsMeta vsMeta)

symbol'eq mx my         = MApp (MPrm "symbol'eq")       [mx, my]

party'eq  mx my         = MApp (MPrm "party'eq")        [mx, my]

nat'add nx ny           = MApp (MPrm "nat'add")         [nx, ny]
nat'eq  nx ny           = MApp (MPrm "nat'eq")          [nx, ny]
nat'le  nx ny           = MApp (MPrm "nat'le")          [nx, ny]
nat'ge  nx ny           = MApp (MPrm "nat'ge")          [nx, ny]

text'eq tx ty           = MApp (MPrm "text'eq")         [tx, ty]

auth'one mp             = MApp (MPrm "auth'one")        [mp]
auth'union ma mb        = MApp (MPrm "auth'union")      [ma, mb]



-- Run --------------------------------------------------------------------------------------------
-- | Try to fire a single rule, printing the first available firing.
runFire :: Auth -> Store -> Rule () -> IO ()
runFire auth store rule
 = case applyFire auth store rule of
        []      -> putStrLn "* Fizz"

        [(dsSpent, dsNew, store')]
         -> do  putStrLn $ (P.displayS $ renderMax $ ppFiring dsSpent dsNew store') ""

        _       -> putStrLn "* Many"


renderMax = P.renderPretty 1.0 100