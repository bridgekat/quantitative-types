import checker

namespace quantitative_types

open idx
open expr
open mult
open ctx

-- Examples adapted from ApiMu (FOLContext).
def bv := var 0 ∘ bound
def fv := var 0 ∘ free
def prop := sort 0
def type := sort 1
def bin := λ a f b, app (app f a) b

def c₁ :=
  ⟦0 • (pi 0 (fv 0) 0 $ pi 0 (fv 0) 0 prop)⟧ :: -- [13] mem : setvar → setvar → Prop
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

def and := fv 6
def iff := fv 9
def for := app (fv 10) ∘ lam 0 (fv 0)
def exi := app (fv 11) ∘ lam 0 (fv 0)
def mem := fv 13

def e₁ :=
  (lam 0 (pi 0 (fv 0) 0 $ pi 0 (fv 0) 0 prop)
    (for $ exi $ for $
      (bin (bin (bv 0) mem (bv 1))
       iff (bin (bin (bv 0) mem (bv 2))
            and (app (app (bv 3) (bv 2)) (bv 0))))))

-- Example on lifetime management.
def use_bv := var free ∘ bound
def read_bv := var read ∘ bound
def write_bv := var write ∘ bound
def use_fv := var free ∘ free
def read_fv := var read ∘ free
def write_fv := var write ∘ free

def c₂ :=
  ⟦free • (pi free (fv 1) 0 (fv 0))  ⟧ :: -- [8]  free     : f•(f•T → Unit)
  ⟦free • (pi write (fv 1) free $ pi free (fv 1) 0 (fv 0))⟧
                                       :: -- [7]  move     : f•(w•T → f•T → Unit)
  ⟦free • (pi all (fv 1) free (fv 1))⟧ :: -- [6]  init     : f•(a•T → f•T)
  ⟦free • (pi write (fv 1) 0 (fv 0)) ⟧ :: -- [5]  update   : f•(w•T → Unit)
  ⟦free • (pi read (fv 1) 0 (fv 0))  ⟧ :: -- [4]  observe  : f•(r•T → Unit)
  ⟦all  • (fv 1)                     ⟧ :: -- [3]  uninitialised : a•T
  ⟦free • (fv 1)                     ⟧ :: -- [2]  object   : f•T
  ⟦0    • type                       ⟧ :: -- [1]  T        : Type
  ⟦0    • type                       ⟧    -- [0]  Unit     : Type

local infixr `;; `:max := expr.letr
def e₂ :=
  (app (use_fv 6) (var all $ free 3));;      -- x ← init [3]
  (app (use_fv 4) (read_bv 0));;             -- observe x
  (app (use_fv 5) (write_fv 2));;            -- update [2]
  (bin (write_bv 2) (use_fv 7) (use_fv 2));; -- x := [2]
  (app (use_fv 8) (use_bv 3))                -- free x

meta def main : io unit := do
{ io.put_str_ln c₂.show,
  io.put_str_ln e₂.show,
  io.put_str_ln "",
  match e₂.check c₂ with
  | (sum.inl msg)    := io.put_str_ln $ "Error: " ++ msg
  | (sum.inr (π, t)) := io.put_str_ln t.show
  end,
  io.put_str_ln "",
  return () }

#eval main

end quantitative_types
