namespace quantitative_types

-- Variables (de Bruijn indices and levels)
@[derive decidable_eq]
inductive idx : Type
| bound : nat → idx
| free  : nat → idx

-- Expressions
@[derive decidable_eq]
inductive expr : Type
| sort : nat →         expr
| var  : idx →         expr
| app  : expr → expr → expr
| lam  : expr → expr → expr
| pi   : expr → expr → expr

def type := expr
def ctype := list type

-- Multiplicities
@[derive decidable_eq]
inductive mult : Type
| zero : mult
| one  : mult
| many : mult

-- Contexts
@[derive decidable_eq]
inductive ctx : ctype → Type
| nil  :                                              ctx []
| cons : Π {γ : ctype} (t : type) (π : mult), ctx γ → ctx (t :: γ)

end quantitative_types
