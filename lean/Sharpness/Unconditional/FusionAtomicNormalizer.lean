import Sharpness.Unconditional.FusionAtomicAction
import Sharpness.Unconditional.AlperinCentric

/-! A proper overgroup of a centric subgroup has nontrivial isotropy in
the outer-automorphism action. This is the support calculation in BLO 3.2. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {L T : Subgroup S} (hLT : L ≤ T)

/-- For a centric subgroup, the kernel of the relative-normalizer action
on its orbit automorphisms consists exactly of the subgroup itself. -/
theorem relativeNormalizerToAut_eq_one_iff
    (hcent : Subgroup.centralizer (L : Set S) ≤ L)
    (n : F.relativeNormalizer T L) :
    F.relativeNormalizerToAut T L n = 1 ↔ n.val ∈ L := by
  constructor
  · intro he
    have heh := congrArg (fun a : Aut (F.toOrbit.obj ⟨L⟩) => a.hom) he
    have hraw : F.toOrbit.map (F.isoOfMulEquiv
        (L.normalizerMonoidHom ⟨n.val, n.property.1⟩)
        (F.normalizerAut_allowed L ⟨n.val, n.property.1⟩)).hom =
      F.toOrbit.map (𝟙 (⟨L⟩ : F.Object)) := heh.trans (F.toOrbit.map_id _).symm
    obtain ⟨r, hr⟩ := (F.orbit_map_eq_iff _ _).mp hraw
    have hc : r.val⁻¹ * n.val ∈ Subgroup.centralizer (L : Set S) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro x hx
      have hh := congrArg (fun y : L => y.val) (hr ⟨x, hx⟩)
      change x = r.val⁻¹ * (n.val * x * n.val⁻¹) * r.val at hh
      have conj : (r.val⁻¹ * n.val) * x * (r.val⁻¹ * n.val)⁻¹ = x := by
        calc
          _ = r.val⁻¹ * (n.val * x * n.val⁻¹) * r.val := by group
          _ = x := hh.symm
      calc
        x * (r.val⁻¹ * n.val) =
          ((r.val⁻¹ * n.val) * x * (r.val⁻¹ * n.val)⁻¹) * (r.val⁻¹ * n.val) := by rw [conj]
        _ = (r.val⁻¹ * n.val) * x := by group
    have hn := L.mul_mem r.property (hcent hc)
    simpa only [mul_inv_cancel_left] using hn
  · intro hn
    exact F.subgroup_killed_by_normalizerAut T L hn

theorem orbitHomStabilizer_inclusion_ne_bot (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (hcent : F.IsCentric L) (proper : L < T) :
    F.orbitHomStabilizer (F.toOrbit.map (F.inclusion hLT)) ≠ ⊥ := by
  have hCT : Subgroup.centralizer (L : Set S) ≤ L := by
    have h := hcent L le_top (MulEquiv.refl L) (F.id_mem L)
    simpa only [inf_top_eq] using h
  have hsmall : L.subgroupOf T ≠ ⊤ := by
    intro heq
    exact proper.not_ge (Subgroup.subgroupOf_eq_top.mp heq)
  have hN := proper_subgroup_lt_normalizer p (hS.to_subgroup T) hsmall
  obtain ⟨n, hnN, hnL⟩ := SetLike.not_le_iff_exists.mp (not_le_of_gt hN)
  have hnS : n.val ∈ Subgroup.normalizer (L : Set S) := by
    have heq := Subgroup.subgroupOf_normalizer_eq hLT
    rw [← heq] at hnN
    exact hnN
  let n' : F.relativeNormalizer T L := ⟨n.val, hnS, n.property⟩
  have hnontrivial : F.relativeNormalizerToAut T L n' ≠ 1 :=
    fun he => hnL ((F.relativeNormalizerToAut_eq_one_iff hCT n').mp he)
  intro heq
  have hm : F.relativeNormalizerToAut T L n' ∈
      F.orbitHomStabilizer (F.toOrbit.map (F.inclusion hLT)) :=
    F.relativeNormalizerToAut_fixes_inclusion hLT n'
  rw [heq] at hm
  exact hnontrivial hm

/-- Off the isomorphism class of a centric source, every orbit of the
automorphism action has nontrivial isotropy. -/
theorem orbitHomStabilizer_ne_bot_of_not_iso (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) {Q P : F.Orbit} (f : Q ⟶ P)
    (hQ : F.IsCentric Q.as.subgroup) (hne : ¬ Nonempty (Q ≅ P)) :
    F.orbitHomStabilizer f ≠ ⊥ := by
  let L := F.arrowImage f
  let e := F.arrowImageIso f
  have hL : F.IsCentric L :=
    F.isoSystem.centricIn_of_iso (F.groupEquivOfOrbitIso e)
      (F.groupEquivOfOrbitIso_allowed e) hQ
  have hproper : L < P.as.subgroup := by
    apply lt_of_le_of_ne (F.arrowImage_le f)
    intro heq
    exact hne ⟨e.trans (F.toOrbit.mapIso (F.subgroupEqualityIso heq))⟩
  have hn := F.orbitHomStabilizer_inclusion_ne_bot (F.arrowImage_le f) p hS hL hproper
  intro hbot
  have hc : (F.orbitHomStabilizer (F.arrowImageInclusion f)).comap
      (Aut.autMulEquivOfIso e).toMonoidHom = ⊥ := by
    rw [← F.orbitHomStabilizer_comp_iso, F.arrow_factorization]
    exact hbot
  apply hn
  apply le_antisymm _ bot_le
  intro a ha
  let τ := Aut.autMulEquivOfIso e
  have hm : τ.symm a ∈ (F.orbitHomStabilizer (F.arrowImageInclusion f)).comap
      τ.toMonoidHom := by
    change τ (τ.symm a) ∈ F.orbitHomStabilizer (F.arrowImageInclusion f)
    rw [τ.apply_symm_apply]
    exact ha
  rw [hc] at hm
  have hh : τ.symm a = 1 := hm
  have hh' := congrArg τ hh
  change a = 1
  simpa only [τ.apply_symm_apply, map_one] using hh'

end Sharpness.FusionSystem
