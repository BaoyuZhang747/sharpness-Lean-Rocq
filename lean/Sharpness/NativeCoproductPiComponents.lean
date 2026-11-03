import Sharpness.NativeCoproductDual

/-! The finite native coproduct-to-product comparison has the identity
matrix on its actual chosen inclusions and coordinate projections. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
    (M : ι → ModuleCat.{max u v} R)

set_option backward.isDefEq.respectTransparency false in
theorem nativeCoproductPiIso_inclusion_self (i : ι) :
    Sigma.ι M i ≫ (nativeCoproductPiIso M).hom ≫ ModuleCat.ofHom (LinearMap.proj i) = 𝟙 (M i) := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp [nativeCoproductPiIso, ModuleCat.ι_coprodIsoDirectSum_hom_apply]

set_option backward.isDefEq.respectTransparency false in
theorem nativeCoproductPiIso_inclusion_other (i j : ι) (h : i≠j) :
    Sigma.ι M i ≫ (nativeCoproductPiIso M).hom ≫ ModuleCat.ofHom (LinearMap.proj j) = 0 := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp [nativeCoproductPiIso, ModuleCat.ι_coprodIsoDirectSum_hom_apply]
  exact DFinsupp.single_eq_of_ne h.symm

end Sharpness
