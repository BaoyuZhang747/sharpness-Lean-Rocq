import Sharpness.Unconditional.NormalizerOrbitPointedImageLaws

/-! Literal carrier-level form of the proved subgroup-image identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.NormalizerSubgroupExtension
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
  {P Q R T : Subgroup S} {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩}

theorem carrier_image_eq (a : F.NormalizerSubgroupExtension R T f) :
    (fun x : a.carrier => (a.extension.val x).val) '' {x | x.val ∈ R} = (a.image : Set S) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact (a.mem_image_iff y).mpr ⟨⟨x.val, hx⟩, hxy⟩
  · intro hy
    obtain ⟨x, hx⟩ := (a.mem_image_iff y).mp hy
    exact ⟨⟨x.val, a.subgroup_le x.property⟩, x.property, hx⟩

end Sharpness.FusionSystem.NormalizerSubgroupExtension
