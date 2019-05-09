
module Rainfall.Source.Exp.Term.Base where
import Rainfall.Core.Exp.Base
import Rainfall.Source.Exp.Type
import Data.Map                 (Map)
import Data.Set                 (Set)


-- | Annotated Term.
data Term a
        = MAnn  a (Term a)                      -- ^ An annotated term.
        | MRef  (TermRef a)                     -- ^ Term reference.
        | MVar  Bound                           -- ^ Term variable.
        | MAbs  [TermParam a] (Term a)          -- ^ Term abstraction.
        | MRec  [TermBind a]  (Term a)          -- ^ Term recursion.
        | MKey  TermKey [TermArg a]             -- ^ Term keyword application.
        deriving (Show, Eq, Ord)


-- | Term binding.
data TermBind a
        = MBind Bind [TermParam a] [Type a] (Term a)
        deriving (Show, Eq, Ord)


-- | Term Reference.
data TermRef a
        = MRPrm Name                            -- ^ Primitive reference.
        | MRCon Name                            -- ^ Data constructor reference.
        | MRVal (Value a)                       -- ^ Value reference.
        deriving (Show, Eq, Ord)


-- | Term Parameter.
data TermParam a
        = MPAnn  a  (TermParam a)
        | MPTerm   (Bind, Type a)               -- ^ Term parameter for a term.
        | MPType   (Bind, Type a)               -- ^ Type parameter for a term.
        deriving (Show, Eq, Ord)


-- | Term Argument.
data TermArg a
        = MGAnn  a  (TermArg a)
        | MGTerm    (Term a)                    -- ^ Term argument for a term.
        | MGTerms   [Term a]                    -- ^ Multiple term arguments for a term.
        | MGType    (Type a)                    -- ^ Type argument for a term.
        deriving (Show, Eq, Ord)


-- | Term Keyword.
data TermKey
        -- | Term formers.
        = MKThe                                 -- ^ Type ascription.
        | MKApp                                 -- ^ Term application.
        | MKLet                                 -- ^ Let expression former.
        | MKCon     Name                        -- ^ Data constructor.
        | MKRecord  [Name]                      -- ^ Record former.
        | MKProject Name                        -- ^ Record field projection.
        | MKVariant Name                        -- ^ Variant former.
        | MKVarCase                             -- ^ Variant case matching.
        | MKVarAlt  Name                        -- ^ Variant case alternative.
        | MKIf                                  -- ^ If-then-else expression.
        | MKList                                -- ^ List constructor.
        | MKSet                                 -- ^ Set constructor.
        | MKMap                                 -- ^ Map constructor.
        | MKSay     Name                        -- ^ Say constructor.
        deriving (Show, Eq, Ord)


-- | Term Value.
--
--   These are really "term normal forms" rather than "values" as type
--   expressions and the bodies of closures may include variable names
--   that refer to top-level things. These names need to be bumped when
--   carrying values under binders.
--
data Value a
        -- Values that are also literals in the source program.
        = VUnit                                 -- ^ Unit value.
        | VBool     Bool                        -- ^ Boolean value.
        | VNat      Integer                     -- ^ Natural value.
        | VInt      Integer                     -- ^ Integer value.
        | VText     String                      -- ^ Text value.
        | VSym      Name                        -- ^ Symbol value.
        | VParty    Name                        -- ^ Party literal.

        -- Values that are only used at runtime.
        --   At runtime they are introduced by evaluating constructions,
        --   and do not appear as literals in the source program.
        --   The annotation on map and set elements is forced to () so that
        --   the order of values in the collection does not depend on the
        --   annotation.
        | VData     Name [Type a] [Value a]     -- ^ Constructed data.
        | VRecord   [(Name, [Value a])]         -- ^ Record value.
        | VVariant  Name (Type a) [Value a]     -- ^ Variant value.
        | VList     (Type a) [Value a]          -- ^ List value.
        | VSet      (Type a) (Set (Value ()))   -- ^ Set value.
        | VMap      (Type a) (Type a) (Map (Value ()) (Value a))
                                                -- ^ Map value.
        | VClosure  (TermClosure a)             -- ^ Closure.
        deriving (Show, Eq, Ord)


-- | Closure value.
data TermClosure a
        = TermClosure (TermEnv a) [TermParam a] (Term a)
        deriving (Show, Eq, Ord)


-- | Environments captured in term closures.
data TermEnv a
        = TermEnv [TermEnvBinds a]
        deriving (Show, Eq, Ord)


-- | Bindings in environments.
data TermEnvBinds a
        = TermEnvTypes          (Map Name (Type a))
        | TermEnvValues         (Map Name (Value a))
        | TermEnvValuesRec      (Map Name (TermClosure a))
        deriving (Show, Eq, Ord)


-- | Normal form arguments for a function application.
--   Argument can be closed types as well as values.
data TermNormals a
        = NTs [Type a]
        | NVs [Value a]
        deriving (Show, Eq, Ord)
