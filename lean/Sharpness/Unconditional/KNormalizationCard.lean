import Sharpness.Unconditional.KNormalization

/-! The kernel-and-image order formula for the K-normalizer. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem kNormalizer_card (P : Subgroup S) (K : Subgroup (F.automorphismSubgroup P)) :
    Nat.card (F.kNormalizer P K) =
      Nat.card (Subgroup.centralizer (P : Set S)) *
        Nat.card (F.kNormalizerToAut P K).range := by
  let f := F.kNormalizerToAut P K
  have hk : Nat.card f.ker = Nat.card (Subgroup.centralizer (P : Set S)) := by
    rw [F.kNormalizerToAut_ker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (F.centralizer_le_kNormalizer P K)).toEquiv
  calc
    Nat.card (F.kNormalizer P K) =
        Nat.card ((F.kNormalizer P K) ⧸ f.ker) * Nat.card f.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    _ = Nat.card f.range * Nat.card f.ker := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    _ = Nat.card (Subgroup.centralizer (P : Set S)) * Nat.card f.range := by
      rw [hk, mul_comm]

end Sharpness.FusionSystem
