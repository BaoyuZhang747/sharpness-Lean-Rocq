import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! The actual mapping cone of a monomorphism computes the cohomology
of its actual cokernel complex. This is the native short-exact-sequence
quasi-isomorphism, with its formula on the target summand. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) [Mono f]

def monoCokernelShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk f (cokernel.π f) (cokernel.condition f)

theorem monoCokernelShortComplex_shortExact : (monoCokernelShortComplex f).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)
  mono_f := inferInstanceAs (Mono f)
  epi_g := inferInstanceAs (Epi (cokernel.π f))

def monoMappingConeToCokernel : CochainComplex.mappingCone f ⟶ cokernel f :=
  CochainComplex.mappingCone.descShortComplex (monoCokernelShortComplex f)

theorem monoMappingConeToCokernel_inr :
    CochainComplex.mappingCone.inr f ≫ monoMappingConeToCokernel f = cokernel.π f :=
  CochainComplex.mappingCone.inr_descShortComplex (monoCokernelShortComplex f)

def monoMappingConeCokernelCohomologyIso (n : ℤ) :
    (CochainComplex.mappingCone f).homology n ≅ (cokernel f).homology n := by
  letI : QuasiIso (monoMappingConeToCokernel f) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex (monoCokernelShortComplex_shortExact f)
  exact isoOfQuasiIsoAt (monoMappingConeToCokernel f) n

end Sharpness
