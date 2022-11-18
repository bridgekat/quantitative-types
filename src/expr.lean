import defs

namespace quantitative_types

open idx
open expr

def idx.show : idx → string
| (bound id) := "$b" ++ to_string id
| (free id)  := "$f" ++ to_string id

instance : has_to_string idx := ⟨idx.show⟩
instance : has_repr idx := ⟨idx.show⟩

def expr.show : expr → string
| (sort s)  := "Sort " ++ to_string s
| (var v)   := v.show
| (app l r) := "(" ++ l.show ++ " " ++ r.show ++ ")"
| (lam t r) := "(\\$: " ++ t.show ++ " => " ++ r.show ++ ")"
| (pi t r)  := "($: " ++ t.show ++ " -> " ++ r.show ++ ")"

instance : has_to_string expr := ⟨expr.show⟩
instance : has_repr expr := ⟨expr.show⟩

def expr.update_vars : expr → (nat → idx → expr) → nat → expr
| (sort s)  f n := sort s
| (var v)   f n := f n v
| (app l r) f n := app (l.update_vars f n) (r.update_vars f n)
| (lam t r) f n := lam (t.update_vars f n) (r.update_vars f (n + 1))
| (pi t r)  f n := pi (t.update_vars f n) (r.update_vars f (n + 1))

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
| (sort s)  := sort s
| (var v)   := var v
| (app l r) :=
  let l := l.reduce, r := r.reduce in
    match l with
    | (lam lt lr) := (lr.make_replace r).reduce 
    | _           := app l r
    end
| (lam t r) := lam t.reduce r.reduce
| (pi t r)  := pi t.reduce r.reduce

def expr.size : expr → int
| (sort s)  := 1
| (var v)   := 1
| (app l r) := l.size + r.size + 1
| (lam t r) := t.size + r.size + 1
| (pi t r)  := t.size + r.size + 1

end quantitative_types
