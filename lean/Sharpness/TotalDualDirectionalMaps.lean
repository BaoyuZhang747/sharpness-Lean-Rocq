import Sharpness.TotalDualProjectionExt
import Sharpness.ChainTotalOutgoing

/-! The actual horizontal/vertical components of the differential on
Hom of the chain total are precomposition by the two actual chain-total
differentials. No differential-transposition property is an input. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (A : ModuleCat.{u} R)

def totalDualHorizontalMap (n : ℕ) :
    ModuleCat.of R ((K.total (ComplexShape.down ℕ)).X n ⟶ A) ⟶
      ModuleCat.of R ((K.total (ComplexShape.down ℕ)).X (n+1) ⟶ A) :=
  ModuleCat.ofHom (Linear.leftComp R A (K.D₁ (ComplexShape.down ℕ) (n+1) n))

def totalDualVerticalMap (n : ℕ) :
    ModuleCat.of R ((K.total (ComplexShape.down ℕ)).X n ⟶ A) ⟶
      ModuleCat.of R ((K.total (ComplexShape.down ℕ)).X (n+1) ⟶ A) :=
  ModuleCat.ofHom (Linear.leftComp R A (K.D₂ (ComplexShape.down ℕ) (n+1) n))

set_option backward.isDefEq.respectTransparency false in
theorem totalDualDifferential_eq_add (n : ℕ) :
    (ChainComplex.linearYonedaObj (K.total (ComplexShape.down ℕ)) R A).d n (n+1) =
      totalDualHorizontalMap K A n + totalDualVerticalMap K A n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (K.total (ComplexShape.down ℕ)).d (n+1) n ≫ f =
    K.D₁ (ComplexShape.down ℕ) (n+1) n ≫ f + K.D₂ (ComplexShape.down ℕ) (n+1) n ≫ f
  rw [HomologicalComplex₂.total_d, Preadditive.add_comp]

end Sharpness
