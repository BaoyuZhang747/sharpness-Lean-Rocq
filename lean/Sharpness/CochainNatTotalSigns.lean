import Mathlib.Algebra.Homology.ComplexShapeSigns

/-! The actual first-quadrant cochain totalization has horizontal sign 1
and vertical sign (-1)^p in bidegree (p,q). -/
set_option autoImplicit false
namespace Sharpness

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance cochainNatTensorSigns : ComplexShape.TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun (i : ℕ) => (-1 : ℤˣ) ^ i) (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : p + 1 = q) := by dsimp; omega
  add_rel p q r (hpq : p + 1 = q) := by dsimp; omega
  ε'_succ := by
    rintro p _ rfl
    dsimp
    rw [pow_add, pow_one, mul_neg, mul_one]

theorem cochainNatTotalDegree (p q : ℕ) :
    ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p,q) =
      p + q := rfl

theorem cochainNatTotalHorizontalSign (p q : ℕ) :
    ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p,q) =
      1 := rfl

theorem cochainNatTotalVerticalSign (p q : ℕ) :
    ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p,q) =
      (-1 : ℤˣ)^p := rfl

end Sharpness
