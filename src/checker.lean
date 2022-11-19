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

def ctx.try_nth {γ : ctype} (Γ : ctx γ) (n : nat) : string ⊕ (expr × mult) :=
  match Γ.nth n with
  | option.none       := sum.inl $ "variable " ++ to_string n ++ " not found in context:\n" ++ Γ.show
  | (option.some res) := sum.inr res
  end

/-- Check if the subtree is a well-formed term (1), type (2), proof (3) or formula (4).
    (1) Returns a well-formed, beta-reduced expression of type `Type`, representing the type of the term;
    (2) Returns `Type` itself;
    (3) Returns a well-formed, beta-reduced expression of type `Prop`, representing the proposition it proves;
    (4) Returns `Prop` itself. -/
def expr.check {γ : ctype} (env : ctx γ) : expr → Π {δ : ctype}, ctx δ → string ⊕ (expr × mult)
| (sort s) δ stk := sum.inr (sort (s + 1), 0) -- TODO
| (var (bound b)) δ stk := stk.try_nth b -- TODO
| (var (free f)) δ stk := env.try_nth (env.length - 1 - f) -- TODO
| (app e₁ e₂) δ stk := do
  { ⟨t₁, π₁⟩ ← e₁.check stk,
    p        ← t₁.as_pi,
    ⟨t₂, π₂⟩ ← e₂.check stk,
    if p.fst = t₂
    then return (p.snd.snd.make_replace e₂, 0) -- TODO
    else sum.inl $ "argument type mismatch: " ++ p.fst.show ++ " != " ++ t₂.show }
| (lam e₁ π e₂) δ stk := do
  { ⟨t₁, π₁⟩ ← e₁.check stk,
    _        ← t₁.as_sort,
    ⟨t₂, π₂⟩ ← e₂.check (cons e₁ 0 stk), -- TODO
    return (pi e₁ π t₂, 0) } -- TODO
| (pi e₁ π e₂) δ stk := do
  { ⟨t₁, π₁⟩ ← e₁.check stk,
    s₁       ← t₁.as_sort,
    ⟨t₂, π₂⟩ ← e₂.check (cons e₁ 0 stk), -- TODO
    s₂       ← t₂.as_sort,
    return (sort (expr.imax s₁ s₂), 0) } -- TODO

end quantitative_types
