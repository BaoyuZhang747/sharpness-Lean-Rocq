import Sharpness.CentralQuotientDefinition

/-! Exact image lifting for actual fusion maps between overgroups of Z.
Fixing Z implies that the projection kernel is contained in each image. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    {A C : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z C⟩)

include hZ

theorem subgroupProjection_kernel_le_range : (F.subgroupProjection Z C).ker ≤ f.val.range := by
  intro x hx
  have hxq : (QuotientGroup.mk x.val : S ⧸ Z) = 1 :=
    congrArg (fun c : C => c.val) hx
  have hxZ : x.val ∈ Z := (QuotientGroup.eq_one_iff x.val).mp hxq
  let xA : F.quotientPreimage Z A := ⟨x.val, (QuotientGroup.le_comap_mk' Z A) hxZ⟩
  refine ⟨xA, ?_⟩
  apply Subtype.ext
  exact F.central_fixed_element hZ f.val f.property xA hxZ

theorem quotient_image_iff (x : F.quotientPreimage Z C) :
    F.subgroupProjection Z C x ∈ (F.quotientInducedHom hZ f).range ↔ x ∈ f.val.range := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨aP, rfl⟩ := F.subgroupProjection_surjective Z A a
    rw [F.quotientInducedHom_apply] at ha
    have hz : (f.val aP)⁻¹ * x ∈ (F.subgroupProjection Z C).ker := by
      change (F.subgroupProjection Z C) ((f.val aP)⁻¹ * x) = 1
      rw [map_mul, map_inv, ha, inv_mul_cancel]
    have hm := f.val.range.mul_mem (show f.val aP ∈ f.val.range from ⟨aP, rfl⟩)
      (F.subgroupProjection_kernel_le_range hZ f hz)
    simpa only [mul_inv_cancel_left] using hm
  · rintro ⟨aP, rfl⟩
    exact ⟨F.subgroupProjection Z A aP, F.quotientInducedHom_apply hZ f aP⟩

theorem quotient_range_projection : f.val.range.map (F.subgroupProjection Z C) =
    (F.quotientInducedHom hZ f).range := by
  ext c
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨F.subgroupProjection Z A a, F.quotientInducedHom_apply hZ f a⟩
  · rintro ⟨a, ha⟩
    obtain ⟨aP, rfl⟩ := F.subgroupProjection_surjective Z A a
    refine ⟨f.val aP, ⟨aP, rfl⟩, ?_⟩
    exact (F.quotientInducedHom_apply hZ f aP).symm.trans ha

end Sharpness.FusionSystem
