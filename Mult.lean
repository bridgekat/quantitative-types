inductive Mult where
  | zero | one | many

protected def Mult.ofNat : Nat → Mult
  | 0 => zero
  | 1 => one
  | _ => many

instance (n : Nat) : OfNat Mult n where
  ofNat := Mult.ofNat n

protected def Mult.add : Mult → Mult → Mult
  | zero, a   => a
  | one, zero => one
  | _, _      => many

instance : Add Mult := ⟨Mult.add⟩
