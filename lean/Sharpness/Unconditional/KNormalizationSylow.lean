import Sharpness.Unconditional.KNormalization

/-! Choosing a fusion conjugate whose K-automizer is Sylow. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness.FusionSystem
open scoped Pointwise
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem mem_range_kNormalizerToAut_iff (P : Subgroup S)
    (K : Subgroup (F.automorphismSubgroup P)) (a : K) :
    a ∈ (F.kNormalizerToAut P K).range ↔ a.val.val ∈ F.innerSylowSubgroup P := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x.val, F.kNormalizer_le_normalizer P K x.property⟩, rfl⟩
  · rintro ⟨n, hn⟩
    have hna : F.kNormalizerAction P n = a.val := Subtype.ext hn
    have hnK : F.kNormalizerAction P n ∈ K := hna ▸ a.property
    let x : F.kNormalizer P K :=
      ⟨n.val, (F.mem_kNormalizer_iff P K n.val).mpr ⟨n.property, hnK⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hna

theorem kNormalizerToAut_range_isPGroup (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S)
    (P : Subgroup S) (K : Subgroup (F.automorphismSubgroup P)) :
    IsPGroup p (F.kNormalizerToAut P K).range :=
  (hS.to_subgroup (F.kNormalizer P K)).of_surjective
    (F.kNormalizerToAut P K).rangeRestrict (F.kNormalizerToAut P K).rangeRestrict_surjective

theorem exists_fullyCentralized_kTransport_sylow (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (P : Subgroup S)
    (K : Subgroup (F.automorphismSubgroup P)) :
    ∃ (Q : Subgroup S) (e : P ≃* Q) (he : F.IsHom e.toMonoidHom),
      F.FullyCentralized Q ∧ ¬ p ∣ (F.kNormalizerToAut Q (F.kTransport e he K)).range.index := by
  obtain ⟨Q, e, he, hQ⟩ := F.exists_fullyNormalized P
  let τ := F.alperinAutTransport e he
  let H : Sylow p K := Classical.choice inferInstance
  let j : K →* F.automorphismSubgroup Q := τ.toMonoidHom.comp K.subtype
  have hpH : IsPGroup p ((H : Subgroup K).map j) := H.isPGroup'.map j
  obtain ⟨T, hHT⟩ := hpH.exists_le_sylow
  let HQ := (F.innerSylowSubgroup Q).subgroupOf (F.automorphismSubgroup Q)
  have hpQ : IsPGroup p HQ := (F.conjugation_isPGroup p hS Q).of_equiv
    (Subgroup.subgroupOfEquivOfLe (F.innerSylowSubgroup_le Q)).symm
  let U : Sylow p (F.automorphismSubgroup Q) :=
    hpQ.toSylow (sat.fully_normalized Q hQ).2
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (F.automorphismSubgroup Q) T U
  let ψ := e.trans a.val
  have hψ : F.IsHom ψ.toMonoidHom := F.comp_mem _ _ he a.property
  let K' := F.kTransport ψ hψ K
  let κ : K ≃* K' := K.equivMapOfInjective
    (F.alperinAutTransport ψ hψ).toMonoidHom (F.alperinAutTransport ψ hψ).injective
  let H' : Sylow p K' := H.mapSurjective (f := κ.toMonoidHom) κ.surjective
  have hHrange : (H' : Subgroup K') ≤ (F.kNormalizerToAut Q K').range := by
    change (H : Subgroup K).map κ.toMonoidHom ≤ _
    rintro _ ⟨x, hx, rfl⟩
    apply (F.mem_range_kNormalizerToAut_iff Q K' (κ x)).mpr
    have hxT : τ x.val ∈ (T : Subgroup (F.automorphismSubgroup Q)) :=
      hHT ⟨x, hx, rfl⟩
    have hsmul := Subgroup.smul_mem_pointwise_smul (τ x.val) (MulAut.conj a)
      (T : Subgroup (F.automorphismSubgroup Q)) hxT
    have hconj : a * τ x.val * a⁻¹ ∈ (U : Subgroup (F.automorphismSubgroup Q)) := by
      rw [← ha, Sylow.coe_subgroup_smul]
      simpa only [MulAut.smul_def, MulAut.conj_apply] using hsmul
    have htransport : F.alperinAutTransport ψ hψ x.val ∈ HQ := by
      rw [alperinAutTransport_trans]
      exact hconj
    exact htransport
  have heq : (F.kNormalizerToAut Q K').range = (H' : Subgroup K') :=
    H'.is_maximal' (F.kNormalizerToAut_range_isPGroup p hS Q K') hHrange
  refine ⟨Q, ψ, hψ, (sat.fully_normalized Q hQ).1, ?_⟩
  change ¬ p ∣ (F.kNormalizerToAut Q K').range.index
  rw [heq]
  exact H'.not_dvd_index

end Sharpness.FusionSystem
