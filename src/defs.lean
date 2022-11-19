namespace quantitative_types

-- Variables (de Bruijn indices and levels)
@[derive decidable_eq]
inductive idx : Type
| bound : nat → idx
| free  : nat → idx

-- Expressions (preterms)
@[derive decidable_eq]
inductive expr : Type
| sort : nat →         expr
| var  : idx →         expr
| app  : expr → expr → expr
| lam  : expr → expr → expr
| pi   : expr → expr → expr

-- Multiplicities (we use the 3-element semiring here)
@[derive decidable_eq]
inductive mult : Type
| zero : mult          -- For use in dependent type checking only
| one  : mult          -- Linear assumptions
| many : mult          -- Unrestricted assumptions

-- Contexts
def ctype := list expr

@[derive decidable_eq]
inductive ctx : ctype → Type
| nil  :                                              ctx []
| cons : Π {γ : ctype} (t : expr) (π : mult), ctx γ → ctx (t :: γ)

end quantitative_types
