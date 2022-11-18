import Mult

inductive Expr where
  | var  : Nat →         Expr
  | nat  : Nat →         Expr
  | plus : Expr → Expr → Expr
  | bool : Bool →        Expr
  | and  : Expr → Expr → Expr

inductive Ty where
  | nat | bool

structure Ctx where
  vars: List (Ty × Mult)

#check Ctx.mk [(Ty.nat, Mult.one)]



def hello := "world"
