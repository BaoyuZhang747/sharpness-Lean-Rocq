import Sharpness.Unconditional.AlperinNormalizer
import Mathlib.GroupTheory.Nilpotent

/-! The two strict-overgroup steps in the centric form of Alperin's theorem. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem centralizer_subset_extensionDomain {P Q : Subgroup S} (e : P ≃* Q) :
    (Subgroup.centralizer (P : Set S) : Set S) ⊆ F.extensionDomain e := by
  intro x hx
  refine ⟨⟨x, Subgroup.centralizer_le_normalizer (P : Set S) hx⟩, rfl, 1, ?_⟩
  intro a
  have hfix : P.normalizerMonoidHom
      ⟨x, Subgroup.centralizer_le_normalizer (P : Set S) hx⟩ a = a := by
    apply Subtype.ext
    change x * a.val * x⁻¹ = a.val
    rw [← (Subgroup.mem_centralizer_iff.mp hx) a.val a.property,
      mul_assoc, mul_inv_cancel, mul_one]
  rw [hfix]
  simp

/-- For a fully centralized subgroup, centricity can be checked on that
subgroup alone. This is proved directly from saturation's extension axiom. -/
theorem centric_iff_selfCentralizer_le_of_fullyCentralized (p : ℕ)
    (sat : F.Saturated p) {P : Subgroup S} (hP : F.FullyCentralized P) :
    F.IsCentric P ↔ Subgroup.centralizer (P : Set S) ≤ P := by
  constructor
  · intro h
    simpa only [inf_top_eq] using h P le_top (MulEquiv.refl P) (F.id_mem P)
  · intro hself Q _ e he
    rw [inf_top_eq]
    obtain ⟨N, hQN, hN, f, hf, hext⟩ :=
      sat.extension e.symm (F.inverse_mem e he) hP
    have hCN : Subgroup.centralizer (Q : Set S) ≤ N := by
      intro x hx
      rw [← SetLike.mem_coe, hN]
      exact F.centralizer_subset_extensionDomain e.symm hx
    intro x hx
    let nx : N := ⟨x, hCN hx⟩
    have hfx : (f nx).val ∈ Subgroup.centralizer (P : Set S) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      let q := e ⟨y, hy⟩
      have hfy : (f ⟨q.val, hQN q.property⟩).val = y := by
        rw [hext q]
        exact congrArg Subtype.val (e.symm_apply_apply ⟨y, hy⟩)
      have hcomm : (⟨q.val, hQN q.property⟩ : N) * nx =
          nx * ⟨q.val, hQN q.property⟩ := by
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp hx) q.val q.property
      have h := congrArg (fun z : N => (f z).val) hcomm
      simpa only [map_mul, Subgroup.coe_mul, hfy] using h
    let y : P := ⟨(f nx).val, hself hfx⟩
    have heq : f ⟨(e y).val, hQN (e y).property⟩ = f nx := by
      apply Subtype.ext
      rw [hext (e y)]
      exact congrArg Subtype.val (e.symm_apply_apply y)
    have hxy := congrArg Subtype.val (F.injective f hf heq)
    change (e y).val = x at hxy
    exact hxy ▸ (e y).property

/-- Every automorphism of a fully centralized, noncentric subgroup extends
to a strictly larger subgroup. -/
theorem noncentric_automorphism_extension (p : ℕ) (sat : F.Saturated p)
    {P : Subgroup S} (hP : F.FullyCentralized P) (hnot : ¬ F.IsCentric P)
    (a : MulAut P) (ha : F.IsHom a.toMonoidHom) :
    ∃ (N : Subgroup S) (hPN : P < N) (f : N →* (⊤ : Subgroup S)),
      F.IsHom f ∧ ∀ x : P, (f ⟨x.val, hPN.le x.property⟩).val = (a x).val := by
  have hbad : ¬ Subgroup.centralizer (P : Set S) ≤ P :=
    fun h => hnot ((F.centric_iff_selfCentralizer_le_of_fullyCentralized p sat hP).mpr h)
  obtain ⟨N, hPN, hN, f, hf, hext⟩ := sat.extension a ha hP
  have hCN : Subgroup.centralizer (P : Set S) ≤ N := by
    intro x hx
    rw [← SetLike.mem_coe, hN]
    exact F.centralizer_subset_extensionDomain a hx
  have hlt : P < N := lt_of_le_of_ne hPN (by
    intro h
    exact hbad (h ▸ hCN))
  exact ⟨N, hlt, f, hf, hext⟩

theorem proper_subgroup_lt_normalizer (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) {P : Subgroup S} (hP : P ≠ ⊤) :
    P < Subgroup.normalizer (P : Set S) := by
  letI := hS.isNilpotent
  exact Group.normalizerCondition_of_isNilpotent P (lt_top_iff_ne_top.mpr hP)

end Sharpness.FusionSystem
