namespace quantitative_types
section

/-- Multiplicities (we use the 3-element semiring here.) -/
/-
@[derive decidable_eq]
inductive mult : Type
| zero : mult          -- No "run-time presence": for use in dependent type checking only
| one  : mult          -- Linear resources
| many : mult          -- Unrestricted resources
open mult
-/

@[derive decidable_eq]
inductive mult : Type
| none
| read
| write
| init
| free
| all
| error
open mult

instance : has_zero mult := ⟨none⟩

def mult.show : mult → string
| none  := "∅"
| read  := "read"
| write := "write"
| init  := "init"
| free  := "free"
| all   := "all"
| error := "☒"

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
| sort : nat →                       expr
| var  : mult → idx →                expr
| app  : expr → expr →               expr
| lam  : mult → expr → expr →        expr
| pi   : mult → expr → mult → expr → expr
| letr : expr → expr →               expr
open expr

def expr.show : expr → string
| (sort 0)         := "Prop"
| (sort 1)         := "Type"
| (sort (s + 1))   := "Type " ++ to_string s
| (var π v)        := "(" ++ π.show ++ "•" ++ v.show ++ ")"
| (app l r)        := "(" ++ l.show ++ " " ++ r.show ++ ")"
| (lam π t e)      := "(fun $: " ++ π.show ++ "•" ++ t.show ++ " => " ++ e.show ++ ")"
| (pi π₁ t₁ π₂ t₂) := "($: " ++ π₁.show ++ "•" ++ t₁.show ++ " -> " ++ π₂.show ++ "•" ++ t₂.show ++ ")"
| (letr e₁ e₂)     := "(let $ := " ++ e₁.show ++ " in " ++ e₂.show ++ ")"

instance : has_to_string expr := ⟨expr.show⟩
instance : has_repr expr := ⟨expr.show⟩

/-- Context types -/
def ctype := list expr

/-- Contexts (precontexts) -/
@[derive decidable_eq]
inductive ctx : ctype → Type
| nil  :                                              ctx []
| cons : Π {γ : ctype} (π : mult) (t : expr), ctx γ → ctx (t :: γ)
open ctx

notation `⟦`:max π:max ` • `:max t:max `⟧`:max ` :: `:max Γ:max := cons π t Γ
notation `⟦`:max π:max ` • `:max t:max `⟧`:max                  := cons π t nil

def ctx.show : Π {γ : ctype}, ctx γ → string
| []       nil          := "ctx.nil\n"
| [t]      (cons π _ _) := "⟦" ++ π.show ++ "•" ++ t.show ++ "⟧\n"
| (t :: γ) (cons π _ Γ) := "⟦" ++ π.show ++ "•" ++ t.show ++ "⟧ ::\n" ++ ctx.show Γ 

instance {γ : ctype} : has_to_string (ctx γ) := ⟨ctx.show⟩
instance {γ : ctype} : has_repr (ctx γ) := ⟨ctx.show⟩

end
end quantitative_types
