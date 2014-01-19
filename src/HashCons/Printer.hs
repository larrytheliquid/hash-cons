module HashCons.Printer where
import Text.PrettyPrint.Leijen
import HashCons.BiMap
import HashCons.Term

----------------------------------------------------------------------

pp :: Pretty a => Int -> a -> IO ()
pp i x = putStrLn $ show (indent i (pretty x))
  -- putStrLn $ displayS (renderPretty 0.4 80 (pretty x)) ""

----------------------------------------------------------------------

instance Pretty Expr where
  pretty (EPi nm _A _B) = parens $
    parens (text nm </> text ":" </> pretty _A) </>
    text "→" </>
    pretty _B
  pretty (ELam nm bd) = parens $
    text "λ" </>
    text nm </>
    text "→" </>
    pretty bd
  pretty (EApp f a) = parens $
    pretty f </> pretty a
  pretty (EVar nm) = text nm
  pretty (ELabel nm) = dquotes (text nm)

instance Pretty a => Pretty (BiMap a) where
  pretty g = vcat $ map
    (\(i , v) -> int i </> text "=" </> pretty v)
    (toList g)

instance Pretty Node where
  pretty (NPi nm _A _B) =
    parens (text nm </> text ":" </> pretty _A) </>
    text "→" </>
    pretty _B
  pretty (NLam nm bd) =
    text "λ" </>
    text nm </>
    text "→" </>
    pretty bd
  pretty (NApp f a) =
    pretty f </> pretty a
  pretty (NVar nm) = text nm
  pretty (NLabel nm) = dquotes (text nm)

----------------------------------------------------------------------