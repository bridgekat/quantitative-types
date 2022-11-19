import checker

namespace quantitative_types

open idx
open expr
open mult
open ctx

def bv := var ∘ bound
def fv := var ∘ free
def prop := sort 0
def type := sort 1
def bin := λ a f b, app (app f a) b

-- Examples adapted from ApiMu (FOLContext).
def c₀ :=
  ⟦(pi (pi (fv 0) 0 prop) 0 prop)   · 0⟧ :: -- [12] unique    : (setvar → Prop) → Prop
  ⟦(pi (pi (fv 0) 0 prop) 0 prop)   · 0⟧ :: -- [11] exists    : (setvar → Prop) → Prop
  ⟦(pi (pi (fv 0) 0 prop) 0 prop)   · 0⟧ :: -- [10] forall    : (setvar → Prop) → Prop
  ⟦(pi prop 0 $ pi prop 0 prop)     · 0⟧ :: -- [9]  iff       : Prop → Prop → Prop
  ⟦(pi prop 0 $ pi prop 0 prop)     · 0⟧ :: -- [8]  implies   : Prop → Prop → Prop
  ⟦(pi prop 0 $ pi prop 0 prop)     · 0⟧ :: -- [7]  or        : Prop → Prop → Prop
  ⟦(pi prop 0 $ pi prop 0 prop)     · 0⟧ :: -- [6]  and       : Prop → Prop → Prop
  ⟦(pi prop 0 prop)                 · 0⟧ :: -- [5]  not       : Prop → Prop
  ⟦prop                             · 0⟧ :: -- [4]  false     : Prop
  ⟦prop                             · 0⟧ :: -- [3]  true      : Prop
  ⟦(pi (fv 0) 0 $ pi (fv 0) 0 prop) · 0⟧ :: -- [2]  equals    : setvar → setvar → Prop
  ⟦(fv 0)                           · 0⟧ :: -- [1]  arbitrary : setvar 
  ⟦type                             · 0⟧    -- [0]  setvar    : Type

def c₁ :=
  ⟦(pi (fv 0) 0 $ pi (fv 0) 0 prop) · 0⟧ :: -- [13] mem : setvar → setvar → Prop
  c₀

def and := fv 6
def iff := fv 9
def all := app (fv 10) ∘ lam (fv 0) 0
def exi := app (fv 11) ∘ lam (fv 0) 0
def mem := fv 13

def e₁ :=
  (lam (pi (fv 0) 0 $ pi (fv 0) 0 prop) 0
    (all $ exi $ all $
      (bin (bin (bv 0) mem (bv 1))
       iff (bin (bin (bv 0) mem (bv 2))
            and (app (app (bv 3) (bv 2)) (bv 0))))))

meta def main : io unit := do
{ io.put_str_ln c₁.show,
  io.put_str_ln "",
  io.put_str_ln e₁.show,
  io.put_str_ln "",
  let res := do
  { -- Changing the last argument to 1 will certainly fail:
    -- we cannot make a runtime instance of the "forall" variable!
    t ← e₁.check c₁ 0,
    return t.show },
  match res with
  | (sum.inl msg) := io.put_str_ln $ "Error: " ++ msg
  | (sum.inr res) := io.put_str_ln res
  end,
  io.put_str_ln "",
  return () }

#eval main

end quantitative_types
