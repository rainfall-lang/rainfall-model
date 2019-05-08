
module Rainfall.Core.Codec.Text.Pretty where
import Rainfall.Core.Exp
import Rainfall.Core.Eval.Store
import Text.PrettyPrint.Leijen
import qualified Data.Set       as Set
import qualified Data.Map       as Map

------------------------------------------------------------------------------------------- Name --
ppName :: Name -> Doc
ppName (Name s) = text s


------------------------------------------------------------------------------------------ Value --
ppValue :: Value a -> Doc
ppValue val
 = case val of
        VLit lit        -> ppLit lit
        VPrm n          -> text "#" <> ppName n
        VClo{}          -> text "#CLO"
        VRcd ns vs      -> list [tupled [ppName n, ppValue v] | (n, v) <- zip ns vs ]
        VFact{}         -> text "#FACT"


ppLit :: Lit -> Doc
ppLit lit
 = case lit of
        LUnit           -> text "#unit"
        LBool b         -> if b then text "#true" else text "#false"
        LNat i          -> integer i
        LText s         -> text (show s)
        LParty n        -> text "!" <> ppName n
        LAuth  a        -> text (show a)
        LSym n          -> text "'" <> ppName n
        LRules rs       -> text (show rs)


ppEnv :: Env a -> Doc
ppEnv env
 = encloseSep (char '[') (char ']') (text ", ")
 $ [ppName n <+> text "=" <+> ppValue v | (n, v) <- env ]


ppAuth :: Auth -> Doc
ppAuth aa
 = encloseSep (char '{') (char '}') (char ',')
 $ [ppLit (LParty n) | n <- Set.toList aa ]


ppRules :: [Name] -> Doc
ppRules rs
 = encloseSep (char '{') (char '}') (char ',')
 $ [ppLit (LSym n) | n <- rs ]


------------------------------------------------------------------------------------------- Fact --
ppFact :: Fact a -> Doc
ppFact (Fact n env aBy aObs rsUse)
 = nest 10
 $ vcat [ fill 10 (ppName n) <+> ppEnv env
        , ppAuth aBy <+> ppAuth aObs <+> ppRules rsUse ]


ppFactoid :: Factoid a -> Doc
ppFactoid (Fact n env aBy aObs rsUse, nWeight)
 = nest 10
 $ vcat [ fill 10 (ppName n) <> ppEnv env
        , text "by " <+> ppAuth aBy    <+> text "obs" <+> ppAuth aObs
        , text "use" <+> ppRules rsUse <+> text "num" <+> integer nWeight ]


------------------------------------------------------------------------------------------ Store --
ppStore :: Store -> Doc
ppStore store
 = vcat
 [ text "(store)"
 , indent 2 $ vcat $ map (\d -> vcat [ppFactoid d, empty]) $ Map.toList store ]


----------------------------------------------------------------------------------------- Firing --
ppFiring :: [Factoid a] -> [Factoid a] -> Store -> Doc
ppFiring dsSpent dsNew store
 = vcat
 [ text "(spend)"
 , indent 2 $ vcat $ map (\d -> vcat [ppFactoid d, empty]) dsSpent
 , text "(new)"
 , indent 2 $ vcat $ map (\d -> vcat [ppFactoid d, empty]) dsNew
 , text "(store)"
 , indent 2 $ vcat $ map (\d -> vcat [ppFactoid d, empty]) $ Map.toList store ]

