
module Rainfall.EDSL
        ( module Rainfall.Core.Exp
        , rule, match
        , rake, rake'facts, rake'when
        , facts, when
        , oneof, anyof, allof, firstof, lastof
        , ret, collect, weight, consume
        , same, acquire
        , unit, bool, sym, nat, text, party, auth, rules
        , (!), pattern (:=)
        , say, symbol'eq, party'eq)
where
import Rainfall.Core.Exp
import Data.String

instance IsString (Term a) where
 fromString s = MVar s

instance IsString Bind where
 fromString s = BindName s


-- Rule -------------------------------------------------------------------------------------------
rule n ms mBody         = Rule n ms mBody
match n r ac mb         = Match n r ac mb

rake g s c              = Rake g s c
rake'facts n g c        = rake (facts n) g c
rake'when n ms g c      = rake (when n ms) g c

facts n                 = GatherWhen n []
when  n ms              = GatherWhen n ms

oneof                   = SelectOne
anyof                   = SelectAny
allof                   = SelectAll
firstof                 = SelectFirst
lastof                  = SelectLast

ret                     = ConsumeRet
collect                 = ConsumeCollect
weight m                = ConsumeWeight m
consume n               = ConsumeWeight (MNat n)

same                    = AcquireSame
acquire m               = AcquireTerm m

-- Term -------------------------------------------------------------------------------------------
unit                    = MUnit
bool  b                 = MBool  b
sym   s                 = MSym   s
nat   n                 = MNat   n
text  t                 = MText  t
party n                 = MParty n
auth  ns                = MAuth  ns
rules ns                = MRules ns

(!) m n                 = MPrj m n
pattern (:=) a b        = (a, b)


-- Prim -------------------------------------------------------------------------------------------
say n nmsFields nmsMeta = MApp (MPrm "say") [MRcd nmsFields, MRcd nmsMeta]

symbol'eq mx my         = MApp (MPrm "symbol'eq") [mx, my]
party'eq  mx my         = MApp (MPrm "party'eq")  [mx, my]




