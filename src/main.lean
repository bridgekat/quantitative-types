import checker

namespace quantitative_types

open idx
open expr
open mult
open ctx

def bv := var 0 ∘ bound
def fv := var 0 ∘ free
def prop := sort 0
def type := sort 1
def bin := λ a f b, app (app f a) b

-- Examples adapted from ApiMu (FOLContext).
def c₀ :=
  ⟦0 • (pi 0 (pi 0 (fv 0) 0 prop) 0 prop)  ⟧ :: -- [12] unique    : (setvar → Prop) → Prop
  ⟦0 • (pi 0 (pi 0 (fv 0) 0 prop) 0 prop)  ⟧ :: -- [11] exists    : (setvar → Prop) → Prop
  ⟦0 • (pi 0 (pi 0 (fv 0) 0 prop) 0 prop)  ⟧ :: -- [10] forall    : (setvar → Prop) → Prop
  ⟦0 • (pi 0 prop 0 $ pi 0 prop 0 prop)    ⟧ :: -- [9]  iff       : Prop → Prop → Prop
  ⟦0 • (pi 0 prop 0 $ pi 0 prop 0 prop)    ⟧ :: -- [8]  implies   : Prop → Prop → Prop
  ⟦0 • (pi 0 prop 0 $ pi 0 prop 0 prop)    ⟧ :: -- [7]  or        : Prop → Prop → Prop
  ⟦0 • (pi 0 prop 0 $ pi 0 prop 0 prop)    ⟧ :: -- [6]  and       : Prop → Prop → Prop
  ⟦0 • (pi 0 prop 0 prop)                  ⟧ :: -- [5]  not       : Prop → Prop
  ⟦0 • prop                                ⟧ :: -- [4]  false     : Prop
  ⟦0 • prop                                ⟧ :: -- [3]  true      : Prop
  ⟦0 • (pi 0 (fv 0) 0 $ pi 0 (fv 0) 0 prop)⟧ :: -- [2]  equals    : setvar → setvar → Prop
  ⟦0 • (fv 0)                              ⟧ :: -- [1]  arbitrary : setvar 
  ⟦0 • type                                ⟧    -- [0]  setvar    : Type

def c₁ :=
  ⟦0 • (pi 0 (fv 0) 0 $ pi 0 (fv 0) 0 prop)⟧ :: -- [13] mem : setvar → setvar → Prop
  c₀

def and := fv 6
def iff := fv 9
def all := app (fv 10) ∘ lam 0 (fv 0)
def exi := app (fv 11) ∘ lam 0 (fv 0)
def mem := fv 13

def e₁ :=
  (lam 0 (pi 0 (fv 0) 0 $ pi 0 (fv 0) 0 prop)
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
    ⟨π, t⟩ ← e₁.check c₁,
    return t.show },
  match res with
  | (sum.inl msg) := io.put_str_ln $ "Error: " ++ msg
  | (sum.inr res) := io.put_str_ln res
  end,
  io.put_str_ln "",
  return () }

#eval main

end quantitative_types
