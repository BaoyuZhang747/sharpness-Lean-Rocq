import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! Actual summand projections in nonnegative chain totalization,
defined by the native total coproduct universal property. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))

def chainTotalProjection (p q n : ℕ) (_h : p+q=n) :
    (K.total (ComplexShape.down ℕ)).X n ⟶ (K.X p).X q := by
  classical
  exact K.totalDesc (fun i j _ =>
    if hij : i=p ∧ j=q then eqToHom (by rw [hij.1, hij.2]) else 0)

set_option backward.isDefEq.respectTransparency false in
theorem chainTotalProjection_inclusion (p q n : ℕ) (h : p+q=n) :
    K.ιTotal (ComplexShape.down ℕ) p q n h ≫ chainTotalProjection K p q n h = 𝟙 _ := by
  classical
  dsimp only [chainTotalProjection]
  rw [HomologicalComplex₂.ι_totalDesc, dif_pos ⟨rfl, rfl⟩]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem chainTotalProjection_other (p q n i j : ℕ) (h : p+q=n) (hij : i+j=n) (hi : i≠p) :
    K.ιTotal (ComplexShape.down ℕ) i j n hij ≫ chainTotalProjection K p q n h = 0 := by
  classical
  dsimp only [chainTotalProjection]
  rw [HomologicalComplex₂.ι_totalDesc, dif_neg (fun he => hi he.1)]

end Sharpness
