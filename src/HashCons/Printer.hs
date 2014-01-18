module HashCons.Printer where
import Text.PrettyPrint.Leijen
import HashCons.Term

----------------------------------------------------------------------

pp :: Pretty a => a -> String
pp x = displayS (renderPretty 0.4 80 (pretty x)) ""

----------------------------------------------------------------------

instance Pretty Expr where
  pretty (EPi nm _A _B) = parens $
    parens (text nm <+> text ":" <+> pretty _A) <+>
    pretty _B
  pretty (ELam nm bd) = parens $
    text "λ" <+>
    text nm <+>
    text "→" <+>
    pretty bd
  pretty (EApp f a) = parens $
    pretty f <+> pretty a
  pretty (EVar nm) = text nm
  pretty (ELabel nm) = dquotes (text nm)

----------------------------------------------------------------------