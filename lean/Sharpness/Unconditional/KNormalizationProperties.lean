import Sharpness.Unconditional.KNormalizationSylow
import Sharpness.Unconditional.KNormalizationCard

/-! The fully K-normalized implication in AKO Proposition I.5.2. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

private theorem card_pSubgroup_le_sylow {G : Type v} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (H : Subgroup G) (hH : IsPGroup p H) (T : Sylow p G) :
    Nat.card H ≤ Nat.card T := by
  obtain ⟨U, hHU⟩ := hH.exists_le_sylow
  exact (Subgroup.card_le_of_le hHU).trans_eq (Nat.card_congr (Sylow.equiv U T).toEquiv)

/-- Full K-normalization implies both full centralization and the Sylow
condition on the actual K-automizer. -/
theorem fullyKNormalized_properties (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S)
    (sat : F.Saturated p) (P : Subgroup S) (K : Subgroup (F.automorphismSubgroup P))
    (hPK : F.FullyKNormalized P K) :
    F.FullyCentralized P ∧ ¬ p ∣ (F.kNormalizerToAut P K).range.index := by
  obtain ⟨Q, e, he, hQ, hSylow⟩ := F.exists_fullyCentralized_kTransport_sylow p hS sat P K
  let K' := F.kTransport e he K
  let κ : K ≃* K' := K.equivMapOfInjective
    (F.alperinAutTransport e he).toMonoidHom (F.alperinAutTransport e he).injective
  let AP := (F.kNormalizerToAut P K).range
  let AQ := (F.kNormalizerToAut Q K').range
  have hpAP : IsPGroup p AP := F.kNormalizerToAut_range_isPGroup p hS P K
  have hpAQ : IsPGroup p AQ := F.kNormalizerToAut_range_isPGroup p hS Q K'
  let T : Sylow p K' := hpAQ.toSylow hSylow
  have hA : Nat.card AP ≤ Nat.card AQ := by
    have hm := card_pSubgroup_le_sylow p (AP.map κ.toMonoidHom)
      (hpAP.map κ.toMonoidHom) T
    rw [Subgroup.card_map_of_injective κ.injective] at hm
    exact hm
  have hC : Nat.card (Subgroup.centralizer (P : Set S)) ≤
      Nat.card (Subgroup.centralizer (Q : Set S)) :=
    hQ P e.symm (F.inverse_mem e he)
  have hmul := hPK Q e he
  rw [F.kNormalizer_card, F.kNormalizer_card] at hmul
  change Nat.card (Subgroup.centralizer (Q : Set S)) * Nat.card AQ ≤
    Nat.card (Subgroup.centralizer (P : Set S)) * Nat.card AP at hmul
  have hAPpos : 0 < Nat.card AP := Nat.card_pos
  have hCPpos : 0 < Nat.card (Subgroup.centralizer (P : Set S)) := Nat.card_pos
  have hAeq : Nat.card AP = Nat.card AQ := by nlinarith
  have hCeq : Nat.card (Subgroup.centralizer (P : Set S)) =
      Nat.card (Subgroup.centralizer (Q : Set S)) := by nlinarith
  have hKeq : Nat.card K = Nat.card K' := Nat.card_congr κ.toEquiv
  have hindex : AP.index = AQ.index := by
    have h1 := AP.card_mul_index
    have h2 := AQ.card_mul_index
    nlinarith
  refine ⟨?_, ?_⟩
  · intro R d hd
    rw [hCeq]
    exact hQ R (e.symm.trans d) (F.comp_mem _ _ (F.inverse_mem e he) hd)
  · change ¬ p ∣ AP.index
    rw [hindex]
    exact hSylow

end Sharpness.FusionSystem
