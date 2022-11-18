import expr
import context

namespace quantitative_types

open idx
open expr
open mult
open ctx

/-- Check if the subtree is a well-formed term (1), type (2), proof (3) or formula (4).
    (1) Returns a well-formed, beta-reduced expression of type `Type`, representing the type of the term;
    (2) Returns `Type` itself;
    (3) Returns a well-formed, beta-reduced expression of type `Prop`, representing the proposition it proves;
    (4) Returns `Prop` itself. -/
def expr.check_type {γ δ : ctype} : expr → ctx γ → ctx δ → bool := sorry

end quantitative_types
