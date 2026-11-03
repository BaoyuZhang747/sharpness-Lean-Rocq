import Sharpness.SubmoduleCochainComplex

/-! Degreewise lifts into an actual differential-stable submodule.
The ambient complex is arbitrary; the lifts retain their literal
inclusion formula and permit cancellation of the subtype inclusion. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R]
    {T : CochainComplex (ModuleCat.{u} R) ℕ}

namespace CochainSubmodules
variable (V : CochainSubmodules T)

def degreeLift {M : ModuleCat.{u} R} (n : ℕ) (f : M ⟶ T.X n)
    (hf : ∀ x, f x ∈ V.term n) : M ⟶ V.complex.X n :=
  ModuleCat.ofHom (f.hom.codRestrict (V.term n) hf)

theorem degreeLift_inclusion {M : ModuleCat.{u} R} (n : ℕ) (f : M ⟶ T.X n)
    (hf : ∀ x, f x ∈ V.term n) :
    V.degreeLift n f hf ≫ V.inclusion.f n = f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem inclusion_component_mono (n : ℕ) : Mono (V.inclusion.f n) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  exact Subtype.val_injective

end CochainSubmodules
end Sharpness
