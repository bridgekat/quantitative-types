import expr
import context

namespace quantitative_types

open idx
open expr
open mult
open ctx

def expr.imax : nat → nat → nat
| 0 _ := 0
| _ 0 := 0
| a b := max a b

def expr.as_sort : expr → string ⊕ nat
| (sort s) := sum.inr s
| e        := sum.inl $ "expression " ++ e.show ++ " is not a sort"

def expr.as_pi : expr → string ⊕ (expr × mult × expr)
| (pi e₁ π e₂) := sum.inr (e₁, π, e₂)
| e            := sum.inl $ "expression " ++ e.show ++ " is not a function"

def ctype.one_nth : Π (γ : ctype), nat → string ⊕ (expr × ctx γ)
| []       _       := sum.inl "undefined variable"
| (t :: _) 0       := sum.inr (t, cons t 1 0)
| (t :: γ) (n + 1) := ctype.one_nth γ n >>= λ ⟨t', Γ⟩, sum.inr (t', cons t 0 Γ)

def ctx.expect_head {γ : ctype} {t : expr} : ctx (t :: γ) → mult → string ⊕ ctx γ
| (cons _ π Γ) π' :=
  if π = π'
  then sum.inr Γ
  else sum.inl "inconsistent multiplicity"

/-- Check if a preterm is a well-formed term (1), type (2), proof (3) or formula (4).
    (1) Returns a well-formed expression of type `sort (n + 1)`, representing the type of the term;
    (2) Returns `sort (n + 1)` itself;
    (3) Returns a well-formed expression of type `sort 0`, representing the proposition it proves;
    (4) Returns `sort 0` itself.
    Also returns the amount of resources required to make *exactly one* instance of the term. -/
meta def expr.check_acc : expr → Π (γ δ : ctype), string ⊕ (expr × ctx γ × ctx δ)
| (sort s)        γ δ := return (sort (s + 1), 0, 0)
| (var (bound b)) γ δ := do ⟨t, Δ⟩ ← δ.one_nth b,                  return (t, 0, Δ)
| (var (free f))  γ δ := do ⟨t, Γ⟩ ← γ.one_nth (γ.length - 1 - f), return (t, Γ, 0)
| (app e₁ e₂)     γ δ := do
  { ⟨t₁, Γ₁, Δ₁⟩  ← e₁.check_acc γ δ,
    ⟨t₁₁, π, t₁₂⟩ ← t₁.as_pi,
    ⟨t₂, Γ₂, Δ₂⟩  ← e₂.check_acc γ δ,
    if t₁₁.reduce = t₂.reduce
    then return (t₁₂.make_replace e₂, Γ₁ + π • Γ₂, Δ₁ + π • Δ₂)
    else sum.inl $ "argument type mismatch: " ++ t₁₁.show ++ " != " ++ t₂.show }
| (lam e₁ π e₂)   γ δ := do
  { ⟨t₁, _⟩       ← e₁.check_acc γ δ,
    _             ← t₁.as_sort,
    ⟨t₂, Γ, Δ⟩    ← e₂.check_acc γ (e₁ :: δ),
    Δ'            ← Δ.expect_head π,
    return (pi e₁ π t₂, Γ, Δ') }
| (pi e₁ π e₂)    γ δ := do
  { ⟨t₁, _⟩       ← e₁.check_acc γ δ,
    s₁            ← t₁.as_sort,
    ⟨t₂, _⟩       ← e₂.check_acc γ (e₁ :: δ),
    s₂            ← t₂.as_sort,
    return (sort (expr.imax s₁ s₂), 0, 0) }

meta def expr.check (e : expr) {γ : ctype} (Γ : ctx γ) (π : mult) : string ⊕ expr := do
{ ⟨t, Γ', Δ'⟩ ← e.check_acc γ [],
  if π • Γ' = Γ
  then return t
  else sum.inl $ "resource mismatch:\nExpected:\n" ++ Γ.show ++ "\nActual:\n" ++ Γ'.show ++ "\n" }

end quantitative_types
