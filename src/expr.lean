import defs

namespace quantitative_types
section

open idx
open expr

def expr.update_vars : expr → (nat → mult → idx → expr) → nat → expr
| (sort s)         f n := sort s
| (var π v)        f n := f n π v
| (app l r)        f n := app (l.update_vars f n) (r.update_vars f n)
| (lam π t e)      f n := lam π (t.update_vars f n) (e.update_vars f (n + 1))
| (pi π₁ t₁ π₂ t₂) f n := pi π₁ (t₁.update_vars f n) π₂ (t₂.update_vars f (n + 1))

/-- Make a free variable into an "overflowed" bound variable. -/
def expr.make_bound : expr → nat → expr
| e s := e.update_vars (λ n π x, if x = free s then var π (bound n) else var π x) 0

/-- Replace one overflow variable by an expression. -/
def expr.make_replace : expr → expr → expr
| e t := e.update_vars (λ n π x, if x = bound n then t else var π x) 0

/-- Performs applicative-order beta-reduction.
    If the original expression is well-typed, the resulting expression will have the same type.
    Note that this function is only a syntactic operation, and does not check well-formedness.
    It does not terminate on inputs like `(fun x => x x x) (fun x => x x x)`. -/
meta def expr.reduce : expr → expr
| (sort s)         := sort s
| (var π v)        := var π v
| (app l r)        :=
  let l := l.reduce,
      r := r.reduce
  in match l with
  | (lam lt lπ lr) := (lr.make_replace r).reduce 
  | _              := app l r
  end
| (lam π t e)      := lam π t.reduce e.reduce
| (pi π₁ t₁ π₂ t₂) := pi π₁ t₁.reduce π₂ t₂.reduce

def expr.size : expr → int
| (sort s)         := 1
| (var π v)        := 1
| (app l r)        := l.size + r.size + 1
| (lam π t e)      := t.size + e.size + 1
| (pi π₁ t₁ π₂ t₂) := t₁.size + t₂.size + 1

end
end quantitative_types
