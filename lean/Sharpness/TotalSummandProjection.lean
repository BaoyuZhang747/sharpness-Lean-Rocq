import Sharpness.FirstQuadrantTotalFiltration

/-! Concrete projections from the actual first-quadrant total module
to one of its summands. The inclusion/projection formulas are proved
from the native coproduct universal property of totalization. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalSummandProjection (p q : ℕ) :
    (K.total (ComplexShape.up ℕ)).X (p+q) ⟶ (K.X p).X q := by
  classical
  exact K.totalDesc (fun i j _ =>
    if h : i = p ∧ j = q then eqToHom (by rw [h.1, h.2]) else 0)

set_option backward.isDefEq.respectTransparency false in
theorem totalSummandProjection_inclusion (p q : ℕ) :
    K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl ≫ totalSummandProjection K p q = 𝟙 _ := by
  classical
  dsimp only [totalSummandProjection]
  rw [HomologicalComplex₂.ι_totalDesc, dif_pos (And.intro rfl rfl)]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem totalSummandProjection_other (p q i j : ℕ) (h : i+j = p+q) (hi : i ≠ p) :
    K.ιTotal (ComplexShape.up ℕ) i j (p+q) h ≫ totalSummandProjection K p q = 0 := by
  classical
  dsimp only [totalSummandProjection]
  rw [HomologicalComplex₂.ι_totalDesc, dif_neg (fun he => hi he.1)]

theorem totalSummandProjection_apply_inclusion (p q : ℕ) (x : (K.X p).X q) :
    totalSummandProjection K p q (K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl x) = x :=
  congrArg (fun f => f x) (totalSummandProjection_inclusion K p q)

theorem totalSummandProjection_apply_other (p q i j : ℕ) (h : i+j = p+q) (hi : i ≠ p)
    (x : (K.X i).X j) :
    totalSummandProjection K p q (K.ιTotal (ComplexShape.up ℕ) i j (p+q) h x) = 0 :=
  congrArg (fun f => f x) (totalSummandProjection_other K p q i j h hi)

end Sharpness
