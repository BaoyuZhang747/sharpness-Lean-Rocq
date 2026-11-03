import Sharpness.V29.SimpleCentralizerTrace
import Sharpness.PrimeFieldMackey

/-! Lemma 2.8(iii) along the manuscript route: the indicated trace-image
summand vanishes; restrictions kill every other summand. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem simple_badCentralizer_of_insideConjugate {Q U : Subgroup S}
    (R L : F.SimpleInclusion Q U) (h : F.simpleInsideConjugate R L)
    (bad : ¬ Subgroup.centralizer (L.val : Set S) ⊓ U ≤ L.val) :
    ¬ Subgroup.centralizer (R.val : Set S) ⊓ U ≤ R.val := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨c, hc, hcL⟩ : ∃ c : S, c ∈ Subgroup.centralizer (L.val : Set S) ⊓ U ∧ c ∉ L.val := by
    simpa only [SetLike.not_le_iff_exists] using bad
  intro hle
  have hdC : t.val * c * t.val⁻¹ ∈ Subgroup.centralizer (R.val : Set S) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    have hccomm := (Subgroup.mem_centralizer_iff.mp hc.1)
      (t.val⁻¹ * x * t.val) ((ht x).mp hx)
    simpa [mul_assoc] using congrArg (fun z : S => t.val * z * t.val⁻¹) hccomm
  have hdU := U.mul_mem (U.mul_mem t.property hc.2) (U.inv_mem t.property)
  have hdR := hle ⟨hdC, hdU⟩
  have hdL := (ht (t.val * c * t.val⁻¹)).mp hdR
  exact hcL (by simpa [mul_assoc] using hdL)

variable {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (hM : M.IsSimple) (Q : Subgroup S) (hQ : F.IsMinimalSupport M Q)

include hM hQ

/-- The relative trace is zero on the actual transported minimal module
used in the Díaz–Park simple functor. -/
theorem simple_transported_trace_zero_v29 (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsPGroup p S) (U : Subgroup S) (L : F.SimpleInclusion Q U)
    (bad : ¬ Subgroup.centralizer (L.val : Set S) ⊓ U ≤ L.val) :
    F.simpleTransportedTrace M Q U L = 0 := by
  ext x
  apply (F.simpleModuleTransport M Q U L).injective
  rw [F.simpleModuleTransport_trace,
    F.normalizerTrace_zero_v29 M p hS (U := U) (L := L.val) L.property.1 bad]
  simp only [LinearMap.zero_apply, map_zero]

theorem simple_diazPark_summand_zero_v29 (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsPGroup p S) (U : Subgroup S) (c : F.SimpleConjugacyClass Q U)
    (bad : ¬ Subgroup.centralizer ((F.simpleClassRepresentative c).val : Set S) ⊓ U ≤
      (F.simpleClassRepresentative c).val) :
    LinearMap.range (F.simpleTransportedTrace M Q U (F.simpleClassRepresentative c)) = ⊥ := by
  rw [F.simple_transported_trace_zero_v29 M hM Q hQ p hS U _ bad, LinearMap.range_zero]

theorem simple_trace_summand_zero_v29 (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsPGroup p S) (U : Subgroup S) (c : F.SimpleConjugacyClass Q U)
    (bad : ¬ Subgroup.centralizer ((F.simpleClassRepresentative c).val : Set S) ⊓ U ≤
      (F.simpleClassRepresentative c).val) :
    F.simpleTraceSummand M Q U c = ⊥ := by
  apply bot_unique
  intro x hx
  let e := F.simpleTransportedTraceRangeEquiv M Q U (F.simpleClassRepresentative c)
  let z : LinearMap.range (F.normalizerTrace M U (F.simpleClassRepresentative c).val) := ⟨x, hx⟩
  have hy : e.symm z = 0 := by
    apply Subtype.ext
    have hm := (e.symm z).property
    exact (F.simple_diazPark_summand_zero_v29 M hM Q hQ p hS U c bad).le hm
  have hz := e.apply_symm_apply z
  rw [hy, map_zero] at hz
  exact (congrArg Subtype.val hz).symm

theorem simple_other_summand_restriction_at (U : Subgroup S)
    (L : F.SimpleInclusion Q U) (d : F.SimpleConjugacyClass Q U)
    (hLd : F.simpleClass L ≠ d) (x : F.simpleTraceSummand M Q U d) :
    M.pull (F.minimalInclusion L) (F.simpleSummandInjection M hM Q hQ U d x) = 0 := by
  let c := F.simpleClass L
  let R := F.simpleClassRepresentative c
  have hc : F.simpleClass R = F.simpleClass L := F.simpleClass_representative c
  let e := F.simpleInsideTransport R L ((F.simpleClass_eq_iff R L).mp hc)
  have he : e.hom ≫ F.minimalInclusion L = F.minimalInclusion R :=
    F.simpleInsideTransport_inclusion R L _
  have hf : F.minimalInclusion L = e.inv ≫ F.minimalInclusion R := by
    rw [← he, Iso.inv_hom_id_assoc]
  rw [hf, M.pull_comp, LinearMap.comp_apply,
    F.simple_other_summand_restriction M hM Q hQ U c d hLd x, map_zero]

/-- The exact characteristic-p restriction-zero endpoint. It is stronger
than Lemma 2.8(iii): saturation is not needed for this trace argument. -/
theorem simple_centralizer_zero_v29 (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsPGroup p S) (L T : Subgroup S)
    (hL : F.isoSystem.IsConjugate Q L) (hLT : L ≤ T)
    (bad : ¬ Subgroup.centralizer (L : Set S) ⊓ T ≤ L) :
    M.pull (F.toOrbit.map (F.inclusion hLT)) = 0 := by
  classical
  letI : Fintype (F.SimpleConjugacyClass Q T) := Fintype.ofFinite _
  let LI : F.SimpleInclusion Q T :=
    ⟨L, hLT, (F.isConjugate_iff_orbit_iso Q L).mp hL⟩
  let c := F.simpleClass LI
  let R := F.simpleClassRepresentative c
  have hc : F.simpleClass R = F.simpleClass LI := F.simpleClass_representative c
  have hbadR := F.simple_badCentralizer_of_insideConjugate R LI
    ((F.simpleClass_eq_iff R LI).mp hc) bad
  have hzero := F.simple_trace_summand_zero_v29 M hM Q hQ p hS T c hbadR
  ext x
  change M.pull (F.minimalInclusion LI) x = 0
  rw [← F.simple_summand_sum M hM Q hQ T x, map_sum]
  apply Finset.sum_eq_zero
  intro d _
  by_cases hd : d = c
  · subst d
    have hw : F.simpleTraceEquiv M hM Q hQ T x c = 0 := by
      apply Subtype.ext
      have hm := (F.simpleTraceEquiv M hM Q hQ T x c).property
      exact hzero.le hm
    rw [hw, map_zero, map_zero]
  · exact F.simple_other_summand_restriction_at M hM Q hQ T LI d (Ne.symm hd) _

omit hM hQ in
/-- The literal saturated prime-field specialisation of v2.9 Lemma 2.8(iii). -/
theorem simple_saturated_centralizer_zero_v29 (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (_sat : F.Saturated p)
    (N : MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape)
    (hN : N.IsSimple) (Q₀ : Subgroup S) (hQ₀ : F.IsMinimalSupport N Q₀)
    (L T : Subgroup S) (hL : F.isoSystem.IsConjugate Q₀ L) (hLT : L ≤ T)
    (bad : ¬ Subgroup.centralizer (L : Set S) ⊓ T ≤ L) :
    N.pull (F.toOrbit.map (F.inclusion hLT)) = 0 :=
  F.simple_centralizer_zero_v29 N hN Q₀ hQ₀ p hS L T hL hLT bad

end Sharpness.FusionSystem
