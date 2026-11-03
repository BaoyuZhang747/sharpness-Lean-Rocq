import Sharpness.CentralSupport

/-! Equivalent extension definitions of a central subgroup of a fusion system. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.V28
variable {S : Type u} [Group S] (F : FusionSystem S)

/-- Every fusion morphism extends over the join, fixing the subgroup pointwise. -/
def CentralExtensionProperty (Z : Subgroup S) : Prop :=
  ∀ {P Q : Subgroup S} (f : P →* Q), F.IsHom f →
    ∃ g : (P ⊔ Z : Subgroup S) →* (Q ⊔ Z : Subgroup S), F.IsHom g ∧
      (∀ x : P, (g ⟨x.val, Subgroup.mem_sup_left x.property⟩).val = (f x).val) ∧
      (∀ z : Z, (g ⟨z.val, Subgroup.mem_sup_right z.property⟩).val = z.val)

/-- Normality together with the pointwise-fixed extension property. -/
def ManuscriptCentralSubgroup (Z : Subgroup S) : Prop :=
  Z.Normal ∧ CentralExtensionProperty F Z

/-- The extension property alone forces the subgroup into the ambient center. -/
theorem centralExtensionProperty_le_center (Z : Subgroup S)
    (h : CentralExtensionProperty F Z) : Z ≤ Subgroup.center S := by
  intro z hz
  apply Subgroup.mem_center_iff.mpr
  intro s
  let f := subgroupConjugation (⊤ : Subgroup S) ⊤ s (fun _ _ => Subgroup.mem_top _)
  obtain ⟨g, _, hgP, hgZ⟩ := h f (F.conjugation_mem _ _ _ _)
  have hfix : s⁻¹ * z * s = z :=
    (hgP ⟨z, Subgroup.mem_top z⟩).symm.trans (hgZ ⟨z, hz⟩)
  have hh := congrArg (s * ·) hfix
  simpa [mul_assoc] using hh.symm

/-- Normality plus extension is equivalent to central containment plus extension. -/
theorem centralSubgroup_iff_manuscriptCentralSubgroup (Z : Subgroup S) :
    F.CentralSubgroup Z ↔ ManuscriptCentralSubgroup F Z := by
  constructor
  · intro hZ
    refine ⟨?_, hZ.extend⟩
    constructor
    intro z hz x
    have hc := Subgroup.mem_center_iff.mp (hZ.in_center hz) x
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact hz
  · intro hZ
    exact ⟨centralExtensionProperty_le_center F Z hZ.2, hZ.2⟩

/-- Convert normality and extension to the central-subgroup structure. -/
def centralSubgroupOfManuscript {Z : Subgroup S} (hZ : ManuscriptCentralSubgroup F Z) :
    F.CentralSubgroup Z :=
  (centralSubgroup_iff_manuscriptCentralSubgroup F Z).mpr hZ

/-- Retain the same extension property and expose ambient normality. -/
def manuscriptCentralSubgroupOfCentral {Z : Subgroup S} (hZ : F.CentralSubgroup Z) :
    ManuscriptCentralSubgroup F Z :=
  (centralSubgroup_iff_manuscriptCentralSubgroup F Z).mp hZ

end Sharpness.FusionSystem.V28
