import Sharpness.TotalSummandProjection

/-! Summand projections at an explicitly specified total degree,
without implicitly rebracketing or rewriting the totalization object. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalSummandProjectionAt (p q n : ℕ) (_h : p+q=n) :
    (K.total (ComplexShape.up ℕ)).X n ⟶ (K.X p).X q := by
  classical
  exact K.totalDesc (fun i j _ =>
    if hij : i=p ∧ j=q then eqToHom (by rw [hij.1,hij.2]) else 0)

set_option backward.isDefEq.respectTransparency false in
theorem totalSummandProjectionAt_inclusion (p q n : ℕ) (h : p+q=n) :
    K.ιTotal (ComplexShape.up ℕ) p q n h ≫ totalSummandProjectionAt K p q n h = 𝟙 _ := by
  classical
  dsimp only [totalSummandProjectionAt]
  rw [HomologicalComplex₂.ι_totalDesc, dif_pos (And.intro rfl rfl)]
  rfl

end Sharpness
