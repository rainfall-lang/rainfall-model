
module Rainfall.EDSL
        ( module Rainfall.Core.Exp
        , rule, match
        , rake, rake'facts, rake'when
        , facts, when
        , anyof, firstof, lastof
        , retain, weight, consume
        , none, gain
        , unit, bool, sym, nat, text, party, auth, rules
        , (!), pattern (:=)

        , say
        , symbol'eq
        , party'eq
        , auth'one, auth'union
        , nat'add, nat'le, nat'ge )
where
import Rainfall.Core.Exp
import Data.String

instance IsString (Term a) where
 fromString s = MVar s

instance IsString (Value a) where
 fromString s = VText s

instance IsString Bind where
 fromString s = BindName s


-- Rule -------------------------------------------------------------------------------------------
rule n ms mBody         = Rule  n ms mBody
match rake acq          = Match rake acq

rake x g s c            = Rake x g s c
rake'facts x n g c      = rake x (facts n) g c
rake'when  x n ms g c   = rake x (when n ms) g c

facts n                 = GatherWhen n []
when  n ms              = GatherWhen n ms

anyof                   = SelectAny
firstof                 = SelectFirst
lastof                  = SelectLast

retain                  = ConsumeRetain
weight m                = ConsumeWeight m
consume n               = ConsumeWeight (MNat n)

none                    = GainNone
gain m                  = GainTerm m


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
say nFact nmsFields nmsMeta
 = let  (nsFields, vsFields)    = unzip nmsFields
        (nsMeta,   vsMeta)      = unzip nmsMeta
   in   MSay nFact (MRcd nsFields vsFields) (MRcd nsMeta vsMeta)

symbol'eq mx my         = MApp (MPrm "symbol'eq")       [mx, my]

party'eq  mx my         = MApp (MPrm "party'eq")        [mx, my]

auth'one mp             = MApp (MPrm "auth'one")        [mp]
auth'union ma mb        = MApp (MPrm "auth'union")      [ma, mb]

nat'add nx ny           = MApp (MPrm "nat'add")         [nx, ny]
nat'le  nx ny           = MApp (MPrm "nat'le")          [nx, ny]
nat'ge  nx ny           = MApp (MPrm "nat'ge")          [nx, ny]

