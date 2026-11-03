import Sharpness.Unconditional.NormalizerOrbitPointedImageBasic

/-! Literal image behavior under composition of actual subgroup extensions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.FusionSystem.NormalizerSubgroupExtension
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
  {P Q W R T U : Subgroup S}
  {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩} {g : (⟨Q⟩ : F.Object) ⟶ ⟨W⟩}

theorem comp_onSubgroup (a : F.NormalizerSubgroupExtension R T f)
    (b : F.NormalizerSubgroupExtension T U g) (x : R) :
    ((a.comp b).extension.val ⟨x.val, (a.comp b).subgroup_le x.property⟩).val =
      (b.extension.val ⟨(a.extension.val ⟨x.val, a.subgroup_le x.property⟩).val,
        b.subgroup_le (a.maps _ x.property)⟩).val := rfl

theorem image_comp_le (a : F.NormalizerSubgroupExtension R T f)
    (b : F.NormalizerSubgroupExtension T U g) : (a.comp b).image ≤ b.image := by
  intro y hy
  obtain ⟨x, rfl⟩ := ((a.comp b).mem_image_iff y).mp hy
  rw [comp_onSubgroup]
  exact (b.mem_image_iff _).mpr
    ⟨⟨(a.extension.val ⟨x.val, a.subgroup_le x.property⟩).val, a.maps _ x.property⟩, rfl⟩

theorem image_comp_eq_of_image_eq (a : F.NormalizerSubgroupExtension R T f)
    (b : F.NormalizerSubgroupExtension T U g) (ha : a.image = T) :
    (a.comp b).image = b.image := by
  apply le_antisymm (image_comp_le a b)
  intro y hy
  obtain ⟨z, hz⟩ := (b.mem_image_iff y).mp hy
  have hzmem : z.val ∈ a.image := ha.symm ▸ z.property
  obtain ⟨x, hx⟩ := (a.mem_image_iff z.val).mp hzmem
  refine ((a.comp b).mem_image_iff y).mpr ⟨x, ?_⟩
  rw [comp_onSubgroup]
  have he : (⟨(a.extension.val ⟨x.val, a.subgroup_le x.property⟩).val,
      b.subgroup_le (a.maps _ x.property)⟩ : b.carrier) =
      ⟨z.val, b.subgroup_le z.property⟩ := Subtype.ext hx
  rw [he]
  exact hz

end Sharpness.FusionSystem.NormalizerSubgroupExtension
