namespace quantitative_types
section

/-- Multiplicities (we use the 3-element semiring here.) -/
@[derive decidable_eq]
inductive mult : Type
| zero : mult          -- No "run-time presence": for use in dependent type checking only
| one  : mult          -- Linear resources
| many : mult          -- Unrestricted resources
open mult

instance : has_zero mult := ⟨zero⟩
instance : has_one mult := ⟨one⟩
notation `ω` := many

def mult.show : mult → string
| 0 := "0"
| 1 := "1"
| ω := "ω"

instance : has_to_string mult := ⟨mult.show⟩
instance : has_repr mult := ⟨mult.show⟩

/-- Bound and free variables (de Bruijn indices and global IDs.) -/
@[derive decidable_eq]
inductive idx : Type
| bound : nat → idx
| free  : nat → idx
open idx

def idx.show : idx → string
| (bound id) := "$" ++ to_string id
| (free id)  := "f" ++ to_string id

instance : has_to_string idx := ⟨idx.show⟩
instance : has_repr idx := ⟨idx.show⟩

/-- Expressions (preterms) -/
@[derive decidable_eq]
inductive expr : Type
| sort : nat →                expr
| var  : idx →                expr
| app  : expr → expr →        expr
| lam  : expr → mult → expr → expr
| pi   : expr → mult → expr → expr
open expr

def expr.show : expr → string
| (sort 0)        := "Prop"
| (sort 1)        := "Type"
| (sort (s + 1))  := "Type " ++ to_string s
| (var v)         := v.show
| (app l r)       := "(" ++ l.show ++ " " ++ r.show ++ ")"
| (lam t π r)     := "(fun $: " ++ t.show ++ " · " ++ π.show ++ " => " ++ r.show ++ ")"
| (pi t π r)      := "($: " ++ t.show ++ " · " ++ π.show ++ " -> " ++ r.show ++ ")"

instance : has_to_string expr := ⟨expr.show⟩
instance : has_repr expr := ⟨expr.show⟩

/-- Context types (precontexts) -/
def ctype := list expr

/-- Contexts -/
@[derive decidable_eq]
inductive ctx : ctype → Type
| nil  :                                              ctx []
| cons : Π {γ : ctype} (t : expr) (π : mult), ctx γ → ctx (t :: γ)
open ctx

notation `⟦` t:max ` · ` π:max `⟧` ` :: ` Γ:90 := cons t π Γ
notation `⟦` t:max ` · ` π:max `⟧`             := cons t π nil

def ctx.show : Π {γ : ctype}, ctx γ → string
| []       nil          := "ctx.nil"
| [t]      (cons _ π _) := "⟦" ++ t.show ++ " · " ++ π.show ++ "⟧"
| (t :: γ) (cons _ π Γ) := "⟦" ++ t.show ++ " · " ++ π.show ++ "⟧ :: \n" ++ ctx.show Γ 

instance {γ : ctype} : has_to_string (ctx γ) := ⟨ctx.show⟩
instance {γ : ctype} : has_repr (ctx γ) := ⟨ctx.show⟩

end
end quantitative_types
