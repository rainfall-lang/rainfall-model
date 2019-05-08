
module Rainfall.Source.Exp.Decl.Base where
import Rainfall.Source.Exp.Type
import Rainfall.Source.Exp.Name

data Decl a
        = DeclFact
        { declFactName          :: Name
        , declFactFields        :: [(Name, Type a)] }
        deriving Show
