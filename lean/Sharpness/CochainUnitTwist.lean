import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! Multiplying every differential by an integer unit does not change
cohomology. The actual cochain isomorphism has component a^n in degree
n, so the sign normalization used for a totalized column is explicit. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R] (V : CochainComplex (ModuleCat.{u} R) ℕ) (a : ℤˣ)

def cochainUnitTwist : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of V.X (fun n => a • V.d n (n+1)) (by
    intro n
    change ((a : ℤ) • V.d n (n+1)) ≫ ((a : ℤ) • V.d (n+1) (n+1+1)) = 0
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, V.d_comp_d, smul_zero, smul_zero])

theorem cochainUnitTwist_d (n : ℕ) :
    (cochainUnitTwist V a).d n (n+1) = a • V.d n (n+1) :=
  CochainComplex.of_d V.X (fun i => a • V.d i (i+1)) n

def cochainUnitTwistIso : V ≅ cochainUnitTwist V a :=
  HomologicalComplex.Hom.isoOfComponents (fun n => a^n • Iso.refl (V.X n)) (by
    intro i j hij
    have hj : i+1 = j := hij
    subst j
    rw [cochainUnitTwist_d]
    change ((a : ℤ)^i • 𝟙 _) ≫ ((a : ℤ) • V.d i (i+1)) =
      V.d i (i+1) ≫ ((a : ℤ)^(i+1) • 𝟙 _)
    simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
      Category.comp_id, Category.id_comp, smul_smul, pow_succ, mul_comm])

def cochainUnitTwistCohomologyIso (n : ℕ) :
    (cochainUnitTwist V a).homology n ≅ V.homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).mapIso
    (cochainUnitTwistIso V a).symm

end Sharpness
