import defs

namespace quantitative_types
section

open idx
open expr

def expr.update_vars : expr → (nat → idx → expr) → nat → expr
| (sort s)    f n := sort s
| (var v)     f n := f n v
| (app l r)   f n := app (l.update_vars f n) (r.update_vars f n)
| (lam t π r) f n := lam (t.update_vars f n) π (r.update_vars f (n + 1))
| (pi t π r)  f n := pi (t.update_vars f n) π (r.update_vars f (n + 1))

/-- Make a free variable into an "overflowed" bound variable. -/
def expr.make_bound : expr → nat → expr
| e s := e.update_vars (λ n x, if x = free s then var (bound n) else var x) 0

/-- Replace one overflow variable by an expression. -/
def expr.make_replace : expr → expr → expr
| e t := e.update_vars (λ n x, if x = bound n then t else var x) 0

/-- Performs applicative-order beta-reduction.
    If the original expression is well-typed, the resulting expression will have the same type.
    Note that this function is only a syntactic operation, and does not check well-formedness.
    It does not terminate on inputs like (\x => x x x) (\x => x x x). -/
meta def expr.reduce : expr → expr
| (sort s)    := sort s
| (var v)     := var v
| (app l r)   :=
  let l := l.reduce, r := r.reduce in
    match l with
    | (lam lt lπ lr) := (lr.make_replace r).reduce 
    | _              := app l r
    end
| (lam t π r) := lam t.reduce π r.reduce
| (pi t π r)  := pi t.reduce π r.reduce

def expr.size : expr → int
| (sort s)    := 1
| (var v)     := 1
| (app l r)   := l.size + r.size + 1
| (lam t π r) := t.size + r.size + 1
| (pi t π r)  := t.size + r.size + 1

end
end quantitative_types
