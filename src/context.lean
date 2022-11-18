import algebra

import type

-- Multiplicities
inductive mult : Type
| zero | one | many

def mult.add : mult → mult → mult
| mult.zero a         := a
| mult.one  mult.zero := mult.one
| _ _                 := mult.many

def mult.mul : mult → mult → mult
| mult.zero _         := mult.zero
| mult.one  a         := a
| mult.many mult.zero := mult.zero
| mult.many _         := mult.many

instance : has_zero mult := ⟨mult.zero⟩
instance : has_one mult := ⟨mult.one⟩
instance : has_add mult := ⟨mult.add⟩
instance : has_mul mult := ⟨mult.mul⟩

@[simp] lemma mult.add_zero (a : mult) : a + 0 = a := by { cases a; refl }
@[simp] lemma mult.zero_add (a : mult) : 0 + a = a := by { cases a; refl }
lemma mult.add_assoc (a b c : mult) : (a + b) + c = a + (b + c) := by { cases a; cases b; cases c; refl }
lemma mult.add_comm (a b : mult) : a + b = b + a := by { cases a; cases b; refl }
@[simp] lemma mult.mul_zero (a : mult) : a * 0 = 0 := by { cases a; refl }
@[simp] lemma mult.zero_mul (a : mult) : 0 * a = 0 := by { cases a; refl }
@[simp] lemma mult.mul_one (a : mult) : a * 1 = a := by { cases a; refl }
@[simp] lemma mult.one_mul (a : mult) : 1 * a = a := by { cases a; refl }
lemma mult.mul_assoc (a b c : mult) : (a * b) * c = a * (b * c) := by { cases a; cases b; cases c; refl }
lemma mult.left_distrib (a b c : mult) : a * (b + c) = a * b + a * c := by { cases a; cases b; cases c; refl }
lemma mult.right_distrib (a b c : mult) : (a + b) * c = a * c + b * c := by { cases a; cases b; cases c; refl }

instance : semiring mult :=
{ zero := mult.zero,
  one := mult.one,
  add := mult.add,
  mul := mult.mul,
  zero_add := mult.zero_add,
  add_zero := mult.add_zero,
  add_assoc := mult.add_assoc,
  add_comm := mult.add_comm,
  mul_zero := mult.mul_zero,
  zero_mul := mult.zero_mul,
  mul_one := mult.mul_one,
  one_mul := mult.one_mul,
  mul_assoc := mult.mul_assoc,
  left_distrib := mult.left_distrib,
  right_distrib := mult.right_distrib }

-- Contexts
def ctype := list type

inductive ctx : ctype → Type
| nil  :                                              ctx []
| cons : Π {γ : ctype} (t : type) (π : mult), ctx γ → ctx (t :: γ)

notation `⟦` t:max ` · ` π:max `⟧` ` :: ` Γ:90 := ctx.cons t π Γ
notation `⟦` t:max ` · ` π:max `⟧`             := ctx.cons t π ctx.nil

def ctx.zero : Π {γ : ctype}, ctx γ
| []       := ctx.nil
| (t :: γ) := ctx.cons t mult.zero ctx.zero

def ctx.one : Π {γ : ctype}, ctx γ
| []       := ctx.nil
| (t :: γ) := ctx.cons t mult.one ctx.one

def ctx.add : Π {γ : ctype}, ctx γ → ctx γ → ctx γ
| _        ctx.nil            ctx.nil            := ctx.nil
| (t :: γ) (ctx.cons _ π₁ Γ₁) (ctx.cons _ π₂ Γ₂) := ctx.cons t (π₁ + π₂) (ctx.add Γ₁ Γ₂)

def ctx.smul : Π {γ : ctype}, mult → ctx γ → ctx γ
| _        _  ctx.nil          := ctx.nil
| (t :: γ) π' (ctx.cons _ π Γ) := ctx.cons t (π' * π) (ctx.smul π' Γ)

instance {γ : ctype} : has_zero (ctx γ) := ⟨ctx.zero⟩
instance {γ : ctype} : has_one (ctx γ) := ⟨ctx.one⟩
instance {γ : ctype} : has_add (ctx γ) := ⟨ctx.add⟩
instance {γ : ctype} : has_smul mult (ctx γ) := ⟨ctx.smul⟩

@[simp] lemma ctx.zero_cons {γ : ctype} {t : type} : (0 : ctx (t :: γ)) = (⟦t · 0⟧ :: (0 : ctx γ)) := rfl
@[simp] lemma ctx.one_cons {γ : ctype} {t : type} : (1 : ctx (t :: γ)) = (⟦t · 1⟧ :: (1 : ctx γ)) := rfl
@[simp] lemma ctx.add_nil {γ : ctype} : ctx.nil + ctx.nil = ctx.nil := rfl
@[simp] lemma ctx.add_cons {γ : ctype} {t : type} {Γ₁ Γ₂ : ctx γ} {π₁ π₂ : mult} :
  ⟦t · π₁⟧ :: Γ₁ + ⟦t · π₂⟧ :: Γ₂ = ⟦t · (π₁ + π₂)⟧ :: (Γ₁ + Γ₂) := rfl
@[simp] lemma ctx.smul_nil {γ : ctype} {π : mult} : π • ctx.nil = ctx.nil := rfl
@[simp] lemma ctx.smul_cons {γ : ctype} {t : type} {Γ : ctx γ} {π' π : mult} :
  π' • ⟦t · π⟧ :: Γ = ⟦t · (π' * π)⟧ :: (π' • Γ) := rfl

lemma ctx.add_comm {γ : ctype} (Γ₁ Γ₂ : ctx γ) : Γ₁ + Γ₂ = Γ₂ + Γ₁ := by
{ induction γ,
  case list.nil : { cases Γ₁, cases Γ₂, refl },
  case list.cons : t γ ih
  { cases Γ₁ with _ _ π₁ Γ₁',
    cases Γ₂ with _ _ π₂ Γ₂',
    simp [ih] at ⊢,
    rw mult.add_comm } }

lemma ctx.add_assoc {γ : ctype} (Γ₁ Γ₂ Γ₃ : ctx γ) : (Γ₁ + Γ₂) + Γ₃ = Γ₁ + (Γ₂ + Γ₃) := by
{ induction γ,
  case list.nil : { cases Γ₁, cases Γ₂, cases Γ₃, refl },
  case list.cons : t γ ih
  { cases Γ₁ with _ _ π₁ Γ₁',
    cases Γ₂ with _ _ π₂ Γ₂',
    cases Γ₃ with _ _ π₃ Γ₃',
    simp [ih] at ⊢,
    rw mult.add_assoc } }

@[simp] lemma ctx.zero_add {γ : ctype} (Γ : ctx γ) : 0 + Γ = Γ := by
{ induction γ,
  case list.nil : { cases Γ, refl },
  case list.cons : t γ ih { cases Γ with _ _ π Γ', simp [ih] at ⊢ } }

@[simp] lemma ctx.add_zero {γ : ctype} (Γ : ctx γ) : Γ + 0 = Γ := by
{ rw ctx.add_comm _ _, exact ctx.zero_add Γ }

instance {γ : ctype} : add_comm_monoid (ctx γ) :=
{ zero := ctx.zero,
  add := ctx.add,
  zero_add := ctx.zero_add,
  add_zero := ctx.add_zero,
  add_assoc := ctx.add_assoc,
  add_comm := ctx.add_comm }

@[simp]
lemma ctx.one_smul {γ : ctype} (Γ : ctx γ) : (1 : mult) • Γ = Γ := by
{ induction γ,
  case list.nil : { cases Γ, refl },
  case list.cons : t γ ih { cases Γ, simp [ih] at ⊢ } }

lemma ctx.mul_smul {γ : ctype} (π₁ π₂ : mult) (Γ : ctx γ) : (π₁ * π₂) • Γ = π₁ • π₂ • Γ := by
{ induction γ,
  case list.nil : { cases Γ, refl },
  case list.cons : t γ ih { cases Γ, simp [ih] at ⊢, rw mult.mul_assoc } }

@[simp]
lemma ctx.smul_zero {γ : ctype} (π : mult) : π • (0 : ctx γ) = 0 := by
{ induction γ,
  case list.nil : { refl },
  case list.cons : t γ ih { simp at ⊢, exact ih } }

lemma ctx.smul_add {γ : ctype} (π : mult) (Γ₁ Γ₂ : ctx γ) : π • (Γ₁ + Γ₂) = π • Γ₁ + π • Γ₂ := by
{ induction γ,
  case list.nil : { cases Γ₁, cases Γ₂, refl },
  case list.cons : t γ ih { cases Γ₁, cases Γ₂, simp [ih] at ⊢, rw mult.left_distrib } }

@[simp]
lemma ctx.zero_smul {γ : ctype} (Γ : ctx γ) : (0 : mult) • Γ = 0 := by
{ induction γ,
  case list.nil : { cases Γ, refl },
  case list.cons : t γ ih { cases Γ, simp [ih] at ⊢ } }

lemma ctx.add_smul {γ : ctype} (π₁ π₂ : mult) (Γ : ctx γ) : (π₁ + π₂) • Γ = π₁ • Γ + π₂ • Γ := by
{ induction γ,
  case list.nil : { cases Γ, refl },
  case list.cons : t γ ih { cases Γ, simp [ih] at ⊢, rw mult.right_distrib } }

instance {γ : ctype} : module mult (ctx γ) :=
{ one_smul := ctx.one_smul,
  mul_smul := ctx.mul_smul,
  smul_zero := ctx.smul_zero,
  smul_add := ctx.smul_add,
  zero_smul := ctx.zero_smul,
  add_smul := ctx.add_smul }
