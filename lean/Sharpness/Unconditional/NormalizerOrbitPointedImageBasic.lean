import Sharpness.Unconditional.NormalizerOrbitPointedSubgroups
import Sharpness.FusionMinimal

/-! Actual image of the normalized subgroup under a concrete simultaneous
extension. The construction retains the actual ambient group elements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.FusionSystem.NormalizerSubgroupExtension
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
  {P Q R T : Subgroup S} {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩}
  (a : F.NormalizerSubgroupExtension R T f)

def subgroupHom : (⟨R⟩ : F.Object) ⟶ ⟨⊤⟩ :=
  F.inclusion a.subgroup_le ≫ a.extension

def image : Subgroup S := F.imageSubgroup a.subgroupHom

theorem mem_image_iff (y : S) : y ∈ a.image ↔
    ∃ x : R, (a.extension.val ⟨x.val, a.subgroup_le x.property⟩).val = y := Iff.rfl

theorem image_le : a.image ≤ T := by
  intro y hy
  obtain ⟨x, rfl⟩ := (a.mem_image_iff y).mp hy
  exact a.maps _ x.property

theorem image_centric (hR : F.IsCentric R) : F.IsCentric a.image := by
  let g : R →* S := (⊤ : Subgroup S).subtype.comp a.subgroupHom.val
  let e := MonoidHom.ofInjective (f := g)
    (Subtype.val_injective.comp (F.injective _ a.subgroupHom.property))
  exact F.isoSystem.centricIn_of_iso e (F.toImage a.subgroupHom).property hR

theorem image_eq_map_subgroupOf :
    a.image = (R.subgroupOf a.carrier).map ((⊤ : Subgroup S).subtype.comp a.extension.val) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := (a.mem_image_iff y).mp hy
    exact ⟨⟨x.val, a.subgroup_le x.property⟩, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (a.mem_image_iff _).mpr ⟨⟨x.val, hx⟩, rfl⟩

theorem image_normalizes (hP : P ≤ Subgroup.normalizer (R : Set S))
    (hf : Function.Surjective f.val) : Q ≤ Subgroup.normalizer (a.image : Set S) := by
  intro q hq
  obtain ⟨x, hx⟩ := hf ⟨q, hq⟩
  rw [a.image_eq_map_subgroupOf]
  apply (R.subgroupOf a.carrier).le_normalizer_map
  refine ⟨⟨x.val, a.acting_le x.property⟩, ?_, ?_⟩
  · rw [← Subgroup.subgroupOf_normalizer_eq a.subgroup_le]
    exact hP x.property
  · change (a.extension.val ⟨x.val, a.acting_le x.property⟩).val = q
    exact (a.onActing x).trans (congrArg Subtype.val hx)

def toImage : F.NormalizerSubgroupExtension R a.image f where
  carrier := a.carrier
  acting_le := a.acting_le
  subgroup_le := a.subgroup_le
  extension := a.extension
  onActing := a.onActing
  maps x hx := (a.mem_image_iff _).mpr ⟨⟨x.val, hx⟩, rfl⟩

end Sharpness.FusionSystem.NormalizerSubgroupExtension
