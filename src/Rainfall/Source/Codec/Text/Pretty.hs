
module Rainfall.Source.Codec.Text.Pretty where
import Rainfall.Source.Exp
import Text.PrettyPrint.Leijen


------------------------------------------------------------------------------------------- Name --
ppName :: Name -> Doc
ppName (Name s) = text s


------------------------------------------------------------------------------------------- Type --
ppType :: Type a -> Doc
ppType tt
 = case tt of
        TFun t1 t2      -> ppType t1 <> text "→" <> ppType t2
        TSet  t         -> text "Set"  <+> ppType t
        TSets t         -> text "Sets" <+> ppType t
        TFact t         -> text "Fact" <+> ppType t
        _               -> ppTypeArg tt


ppTypeArg :: Type a -> Doc
ppTypeArg tt
 = case tt of
        TAnn _ t        -> ppType t
        TRef (TRPrm n)  -> text "#" <> ppName n
        TRef (TRCon n)  -> ppName n
        TVar (Bound n)  -> ppName n

        TBot            -> text "⊥"
        TTop            -> text "⊤"

        TFun{}          -> parens $ ppType tt

        TRcd ns ts
         -> encloseSep (char '[') (char ']') (text ", ")
         $  [ppName n <> text ": " <> ppType t | (n, t) <- zip ns ts]

        TSet{}          -> parens $ ppType tt
        TSets{}         -> parens $ ppType tt
        TFact{}         -> parens $ ppType tt
        TFACT           -> text "FACT"

        _               -> text "?"
