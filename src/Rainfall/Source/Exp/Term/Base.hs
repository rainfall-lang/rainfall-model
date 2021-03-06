
module Rainfall.Source.Exp.Term.Base where
import Rainfall.Core.Exp.Base
import Rainfall.Source.Exp.Type


-- | Annotated Term.
data Term a
        = MAnn  a (Term a)              -- ^ An annotated term.
        | MRef  (TermRef a)             -- ^ Term reference.
        | MVar  Bound                   -- ^ Term variable.
        | MAbs  [TermParam a] (Term a)  -- ^ Term abstraction.
        | MKey  TermKey [TermArg a]     -- ^ Term keyword application.
        deriving (Show, Eq, Ord)


-- | Term Reference.
data TermRef a
        = MRVal Value                   -- ^ Value reference.
        deriving (Show, Eq, Ord)


-- | Term Parameter.
data TermParam a
        = MPAnn  a  (TermParam a)
        | MPTerm   (Bind, Type a)       -- ^ Term parameter for a term.
        | MPType   (Bind, Type a)       -- ^ Type parameter for a term.
        deriving (Show, Eq, Ord)


-- | Term Argument.
data TermArg a
        = MGAnn  a  (TermArg a)
        | MGTerm    (Term a)            -- ^ Term argument for a term.
        | MGTerms   [Term a]            -- ^ Multiple term arguments for term.
        deriving (Show, Eq, Ord)


-- | Term Keyword.
data TermKey
        -- | Term formers.
        = MKPrm  Name                   -- ^ Primitive application.
        | MKApp                         -- ^ Term application.
        | MKRcd  [Name]                 -- ^ Record former.
        | MKPrj  Name                   -- ^ Record field projection.
        | MKSet                         -- ^ Set constructor.
        | MKSay  Name                   -- ^ Say constructor.
        | MKInfix Name                  -- ^ Infix application.
        deriving (Show, Eq, Ord)


-- | Term Value.
data Value
        = VUnit                         -- ^ Unit value.
        | VBool     Bool                -- ^ Boolean value.
        | VNat      Integer             -- ^ Natural value.
        | VText     String              -- ^ Text value.
        | VSym      Name                -- ^ Symbol value.
        | VParty    Name                -- ^ Party literal.
        deriving (Show, Eq, Ord)
