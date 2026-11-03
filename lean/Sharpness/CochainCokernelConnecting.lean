import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Cokernel connecting maps computed on actual cycle lifts. This works
with arbitrary complex shapes and uses the native short-exact sequence. -/
set_option autoImplicit false
noncomputable section
universe u t
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] {ι : Type t} {c : ComplexShape ι}
    {A B : HomologicalComplex (ModuleCat.{u} R) c} (f : A ⟶ B)

def cochainCokernelSequence : ShortComplex (HomologicalComplex (ModuleCat.{u} R) c) :=
  ShortComplex.mk f (cokernel.π f) (cokernel.condition f)

theorem cochainCokernelSequence_shortExact [Mono f] : (cochainCokernelSequence f).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)
  mono_f := inferInstanceAs (Mono f)
  epi_g := inferInstanceAs (Epi (cokernel.π f))

theorem cochainCokernel_projection_cycle {M : ModuleCat.{u} R} (i j : ι)
    (x₂ : M ⟶ B.X i) (x₁ : M ⟶ A.X j)
    (hx : x₁ ≫ f.f j = x₂ ≫ B.d i j) :
    (x₂ ≫ (cokernel.π f).f i) ≫ (cokernel f).d i j = 0 := by
  have hz : f.f j ≫ (cokernel.π f).f j = 0 := by
    have h := HomologicalComplex.congr_hom (cokernel.condition f) j
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using h
  calc
    _ = (x₂ ≫ B.d i j) ≫ (cokernel.π f).f j := by
      rw [Category.assoc, (cokernel.π f).comm]
      exact (Category.assoc _ _ _).symm
    _ = (x₁ ≫ f.f j) ≫ (cokernel.π f).f j := congrArg (fun t => t ≫ (cokernel.π f).f j) hx.symm
    _ = 0 := by rw [Category.assoc, hz, comp_zero]

end Sharpness
