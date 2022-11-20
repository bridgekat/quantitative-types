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

def expr.as_sort : mult → expr → string ⊕ nat
| 0 (sort s) := sum.inr s
| _ (sort s) := sum.inl $ "type does not have multiplicity " ++ mult.none.show
| _ e        := sum.inl $ "expression " ++ e.show ++ " is not a sort"

def expr.as_pi : mult → expr → string ⊕ (mult × expr × mult × expr)
| 0    (pi 0 t₁ 0 t₂)   := sum.inr (0, t₁, 0, t₂)
| free (pi π₁ t₁ π₂ t₂) := sum.inr (π₁, t₁, π₂, t₂)
| _    (pi π₁ t₁ π₂ t₂) := sum.inl $ "function does not have multiplicity " ++ mult.free.show
| _    e                := sum.inl $ "expression " ++ e.show ++ " is not a function"

def ctype.at_nth : Π (γ : ctype), nat → mult → string ⊕ (expr × ctx γ)
| []       _       _ := sum.inl "undefined variable"
| (t :: _) 0       π := sum.inr (t, cons π t 0)
| (t :: γ) (n + 1) π := ctype.at_nth γ n π >>= λ ⟨t', Γ⟩, sum.inr (t', cons 0 t Γ)

def ctx.expect_head {γ : ctype} {t : expr} : ctx (t :: γ) → mult → string ⊕ ctx γ
| (cons π _ Γ) π' :=
  if π = π'
  then sum.inr Γ
  else sum.inl "inconsistent multiplicity"

/-- Check if a preterm is a well-formed term (1), type (2), proof (3) or formula (4).
    (1) Returns a well-formed expression of type `sort (n + 1)`, representing the type of the term;
    (2) Returns `sort (n + 1)` itself;
    (3) Returns a well-formed expression of type `sort 0`, representing the proposition it proves;
    (4) Returns `sort 0` itself.
    Also returns the amount of resources required to make π instances of the term. -/
meta def expr.check_acc : expr → Π (γ δ : ctype), string ⊕ (mult × expr × ctx γ × ctx δ)
| (sort s)            γ δ := return (0, sort (s + 1), 0, 0)
| (var π (bound b))   γ δ := do ⟨t, Δ⟩ ← δ.at_nth b π,                  return (π, t, 0, Δ)
| (var π (free f))    γ δ := do ⟨t, Γ⟩ ← γ.at_nth (γ.length - 1 - f) π, return (π, t, Γ, 0)
| (app l r)           γ δ := do
  { ⟨πl, tl, Γl, Δl⟩  ← l.check_acc γ δ,
    ⟨π₁, t₁, π₂, t₂⟩  ← expr.as_pi πl tl,
    ⟨πr, tr, Γr, Δr⟩  ← r.check_acc γ δ,
    if (π₁ = πr) && (t₁.reduce = tr.reduce)
    then return (π₂, t₂.make_replace r, Γl + Γr, Δl + Δr)
    else sum.inl $ "argument type mismatch: " ++ π₁.show ++ "•" ++ t₁.show ++ " != " ++ πr.show ++ "•" ++ tr.show }
| (lam π t e)         γ δ := do
  { ⟨π', t', _, _⟩    ← t.check_acc γ δ,
    _                 ← expr.as_sort π' t',
    ⟨π₂, t₂, Γ, Δ'⟩   ← e.check_acc γ (t :: δ),
    Δ                 ← Δ'.expect_head π,
    return (if (π = 0) && (π₂ = 0) then 0 else free, pi π t π₂ t₂, Γ, Δ) }
| (pi π₁ t₁ π₂ t₂)    γ δ := do
  { ⟨π', t', _, _⟩    ← t₁.check_acc γ δ,
    s₁                ← expr.as_sort π' t',
    ⟨π'', t'', _, _⟩  ← t₂.check_acc γ (t₁ :: δ),
    s₂                ← expr.as_sort π'' t'',
    return (0, sort (expr.imax s₁ s₂), 0, 0) }
| (letr l r)          γ δ := do
  { ⟨πl, tl, Γl, Δl⟩  ← l.check_acc γ δ,
    ⟨πr, tr, Γr, Δr⟩  ← (lam πl tl r).check_acc γ δ,
    ⟨_, _, π₂, t₂⟩    ← expr.as_pi πr tr,
    return (π₂, t₂, Γl + Γr, Δl + Δr) }

meta def expr.check (e : expr) {γ : ctype} (Γ : ctx γ) : string ⊕ (mult × expr) := do
{ ⟨π, t, Γ', Δ'⟩ ← e.check_acc γ [],
  if Γ' = Γ
  then return (π, t)
  else sum.inl $ "resource mismatch:\nExpected:\n" ++ Γ.show ++ "\nActual:\n" ++ Γ'.show ++ "\n" }

end quantitative_types
