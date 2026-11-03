import Sharpness.FusionStableZero

/-! The central-subgroup support deductions in manuscript Lemma 3.3,
Steps 1 and 2, for actual subgroups and actual full Mackey coefficients. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

/-- The defining extension property of Z <= Z(F), stated with the actual
subgroup join and pointwise equalities of the extending homomorphism. -/
structure CentralSubgroup (Z : Subgroup S) : Prop where
  in_center : Z ≤ Subgroup.center S
  extend : ∀ {P Q : Subgroup S} (f : P →* Q), F.IsHom f →
    ∃ g : (P ⊔ Z : Subgroup S) →* (Q ⊔ Z : Subgroup S), F.IsHom g ∧
      (∀ x : P, (g ⟨x.val, (show P ≤ P ⊔ Z from le_sup_left) x.property⟩).val = (f x).val) ∧
      (∀ z : Z, (g ⟨z.val, (show Z ≤ P ⊔ Z from le_sup_right) z.property⟩).val = z.val)

theorem central_fixed {Z P Q : Subgroup S} (hZ : F.CentralSubgroup Z)
    (f : P →* Q) (hf : F.IsHom f) (hZP : Z ≤ P) (z : Z) :
    (f ⟨z.val, hZP z.property⟩).val = z.val := by
  obtain ⟨g, _, hgP, hgZ⟩ := hZ.extend f hf
  exact (hgP ⟨z.val, hZP z.property⟩).symm.trans (hgZ z)

theorem central_containment_iff {Z P Q : Subgroup S} (hZ : F.CentralSubgroup Z)
    (e : P ≃* Q) (he : F.IsHom e.toMonoidHom) : Z ≤ P ↔ Z ≤ Q := by
  constructor
  · intro hZP z hz
    have h := F.central_fixed hZ e.toMonoidHom he hZP ⟨z, hz⟩
    change (e ⟨z, hZP hz⟩).val = z at h
    rw [← h]
    exact (e ⟨z, hZP hz⟩).property
  · intro hZQ z hz
    have h := F.central_fixed hZ e.symm.toMonoidHom (F.inverse_mem e he) hZQ ⟨z, hz⟩
    change (e.symm ⟨z, hZQ hz⟩).val = z at h
    rw [← h]
    exact (e.symm ⟨z, hZQ hz⟩).property

theorem central_le_centric {Z P : Subgroup S} (hZ : F.CentralSubgroup Z)
    (hP : F.IsCentric P) : Z ≤ P := by
  have h := hP P le_top (MulEquiv.refl P) (F.id_mem P)
  rw [inf_top_eq] at h
  exact (hZ.in_center.trans (Subgroup.center_le_centralizer _)).trans h

variable [Finite S] {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)

/-- The support part of Step 2: if the minimal class contains Z, every
nonzero value must occur at a subgroup containing Z. -/
theorem simple_zero_off_central_overgroups {Z : Subgroup S}
    (hZ : F.CentralSubgroup Z) (hZQ : Z ≤ label.Q.as.subgroup)
    (P : Subgroup S) (hZP : ¬ Z ≤ P) : ∀ x : M.Value (F.toOrbit.obj ⟨P⟩), x = 0 := by
  classical
  have none : IsEmpty (F.MinimalInclusionIndex label.Q (F.toOrbit.obj ⟨P⟩)) := by
    refine ⟨fun L => ?_⟩
    obtain ⟨e⟩ := L.property.2
    have hZL := (F.central_containment_iff hZ (F.groupEquivOfOrbitIso e)
      (F.groupEquivOfOrbitIso_allowed e)).mp hZQ
    exact hZP (hZL.trans L.property.1)
  letI := none
  have hg := F.simple_inclusion_generation M label.Q label.small_zero label.simple
    label.nonzero (F.toOrbit.obj ⟨P⟩)
  simp only [iSup_of_empty] at hg
  intro x
  have hx : x ∈ (⊥ : Submodule k (M.Value (F.toOrbit.obj ⟨P⟩))) := by
    rw [hg]
    exact Submodule.mem_top
  exact hx

/-- Step 1 of Lemma 3.3: a minimal class not containing Z has zero
values on all centric subgroups. Detection and centralizer cancellation
are the proved manuscript results, not additional assumptions. -/
theorem simple_zero_on_centric_of_central_missing
    (DP : F.DiazParkTraceInput (k := k)) (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsPGroup p S) {Z : Subgroup S} (hZ : F.CentralSubgroup Z)
    (hZQ : ¬ Z ≤ label.Q.as.subgroup) (P : Subgroup S) (centric : F.IsCentric P) :
    ∀ x : M.Value (F.toOrbit.obj ⟨P⟩), x = 0 := by
  intro x
  apply (restrictionProduct_injective_iff _).mp
    (F.simple_inclusion_detection M label.Q label.small_zero label.simple label.nonzero
      (F.toOrbit.obj ⟨P⟩)) x
  intro L
  obtain ⟨e⟩ := L.property.2
  have hZL : ¬ Z ≤ L.val := fun h => hZQ
    ((F.central_containment_iff hZ (F.groupEquivOfOrbitIso e)
      (F.groupEquivOfOrbitIso_allowed e)).mpr h)
  have hZP := F.central_le_centric hZ centric
  have bad : ¬ Subgroup.centralizer (L.val : Set S) ⊓ P ≤ L.val := by
    intro hc
    exact hZL ((le_inf (hZ.in_center.trans (Subgroup.center_le_centralizer _)) hZP).trans hc)
  have hz := F.simple_centralizer_zero DP p hS M label P L.val L.property.1 ⟨e⟩ bad
  exact LinearMap.congr_fun hz x

end Sharpness.FusionSystem
