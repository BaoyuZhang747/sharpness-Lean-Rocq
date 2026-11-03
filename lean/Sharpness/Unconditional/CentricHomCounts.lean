import Sharpness.Unconditional.FusionAtomicRepresentability
import Sharpness.Unconditional.AtomicGroupOrbitSylowFusion

/-! Díaz--Libman Proposition 2.8: centric orbit morphism counts, proved by
normalizer induction and the p-group fixed-point congruence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem atomicNormalizerPreimage_relativeNormalizer_range
    {Q T : Subgroup S} (hQT : Q ≤ T) (hQ : F.IsCentric Q) :
    F.atomicNormalizerPreimage Q (F.relativeNormalizerToAut T Q).range =
      F.relativeNormalizer T Q := by
  have hC : Subgroup.centralizer (Q : Set S) ≤ Q := by
    simpa only [inf_top_eq] using hQ Q le_top (MulEquiv.refl Q) (F.id_mem Q)
  ext s
  constructor
  · intro hs
    obtain ⟨hn, n, he⟩ := (F.mem_atomicNormalizerPreimage Q _ s).mp hs
    let m : F.relativeNormalizer (⊤ : Subgroup S) Q :=
      ⟨n.val⁻¹ * s, (Subgroup.normalizer (Q : Set S)).mul_mem
        ((Subgroup.normalizer (Q : Set S)).inv_mem n.property.1) hn, Subgroup.mem_top _⟩
    have hm : F.relativeNormalizerToAut ⊤ Q m = 1 := by
      change F.normalizerToOrbitAut Q
        ((⟨n.val, n.property.1⟩ : Subgroup.normalizer (Q : Set S))⁻¹ * ⟨s, hn⟩) = 1
      rw [map_mul, map_inv]
      change (F.relativeNormalizerToAut T Q n)⁻¹ * _ = 1
      rw [he, inv_mul_cancel]
    have hmem : n.val⁻¹ * s ∈ Q := (F.relativeNormalizerToAut_eq_one_iff hC m).mp hm
    refine ⟨hn, ?_⟩
    change s ∈ T
    simpa only [mul_inv_cancel_left] using T.mul_mem n.property.2 (hQT hmem)
  · intro hs
    exact (F.mem_atomicNormalizerPreimage Q _ s).mpr
      ⟨hs.1, ⟨⟨s, hs⟩, rfl⟩⟩

def atomicFixedMorphismsEquivFixedPoints (Q : Subgroup S)
    (H : Subgroup (Aut (F.toOrbit.obj ⟨Q⟩))) (P : F.Orbit) :
    letI := F.orbitHomAction (F.toOrbit.obj ⟨Q⟩) P
    F.AtomicFixedMorphisms Q H P ≃ MulAction.fixedPoints H (F.toOrbit.obj ⟨Q⟩ ⟶ P) := by
  letI := F.orbitHomAction (F.toOrbit.obj ⟨Q⟩) P
  apply Equiv.subtypeEquivRight
  intro f
  constructor
  · intro hf a
    change a.val.inv ≫ f = f
    exact hf (H.inv_mem a.property)
  · intro hf a ha
    have h := hf (⟨a⁻¹, H.inv_mem ha⟩ : H)
    exact h

theorem centric_hom_count_modEq_normalizer (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {Q T : Subgroup S} (hQT : Q ≤ T) (hQ : F.IsCentric Q) (P : F.Orbit) :
    Nat.card (F.toOrbit.obj ⟨Q⟩ ⟶ P) ≡
      Nat.card (F.toOrbit.obj ⟨F.relativeNormalizer T Q⟩ ⟶ P) [MOD p] := by
  let H := (F.relativeNormalizerToAut T Q).range
  have hH : H ≤ (F.normalizerToOrbitAut Q).range := by
    rintro a ⟨n, rfl⟩
    exact ⟨⟨n.val, n.property.1⟩, rfl⟩
  have hpH : IsPGroup p H := (hS.to_subgroup (F.relativeNormalizer T Q)).of_surjective
    (F.relativeNormalizerToAut T Q).rangeRestrict
    (F.relativeNormalizerToAut T Q).rangeRestrict_surjective
  letI := F.orbitHomAction (F.toOrbit.obj ⟨Q⟩) P
  have hc := hpH.card_modEq_card_fixedPoints (F.toOrbit.obj ⟨Q⟩ ⟶ P)
  have he := (F.atomicFixedRestrictionEquiv Q H p hS sat hQ hH P).trans
    (F.atomicFixedMorphismsEquivFixedPoints Q H P)
  rw [← Nat.card_congr he] at hc
  rw [F.atomicNormalizerPreimage_relativeNormalizer_range hQT hQ] at hc
  exact hc

/-- Every endomorphism in the finite fusion orbit category is invertible. -/
def orbitEndEquivAut (P : F.Orbit) : (P ⟶ P) ≃ Aut P where
  toFun f := by
    letI := F.orbit_isIso_of_equal_order f rfl
    exact asIso f
  invFun a := a.hom
  left_inv _ := rfl
  right_inv a := Iso.ext rfl

/-- Díaz--Libman 2.8, with an arbitrary centric subgroup of the target. -/
theorem centric_hom_count_modEq (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {Q T : Subgroup S} (hQT : Q ≤ T) (hQ : F.IsCentric Q) :
    Nat.card (F.toOrbit.obj ⟨Q⟩ ⟶ F.toOrbit.obj ⟨T⟩) ≡
      Nat.card (Aut (F.toOrbit.obj ⟨T⟩)) [MOD p] := by
  have main : ∀ n : ℕ, ∀ Q : Subgroup S, Nat.card S - Nat.card Q = n →
      Q ≤ T → F.IsCentric Q →
      Nat.card (F.toOrbit.obj ⟨Q⟩ ⟶ F.toOrbit.obj ⟨T⟩) ≡
        Nat.card (Aut (F.toOrbit.obj ⟨T⟩)) [MOD p] := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Q hmeasure hQT hQ
      by_cases heq : Q = T
      · subst Q
        rw [Nat.card_congr (F.orbitEndEquivAut (F.toOrbit.obj ⟨T⟩))]
      let N := F.relativeNormalizer T Q
      have hQN : Q ≤ N := fun x hx => ⟨Q.le_normalizer hx, hQT hx⟩
      have hproper : Q < N := by
        have hsmall : Q.subgroupOf T ≠ ⊤ := by
          intro ht
          exact heq (le_antisymm hQT (Subgroup.subgroupOf_eq_top.mp ht))
        have h := proper_subgroup_lt_normalizer p (hS.to_subgroup T) hsmall
        obtain ⟨x, hxN, hxQ⟩ := SetLike.not_le_iff_exists.mp (not_le_of_gt h)
        have hx : x.val ∈ N := by
          refine ⟨?_, x.property⟩
          rw [← Subgroup.subgroupOf_normalizer_eq hQT] at hxN
          exact hxN
        exact lt_of_le_of_ne hQN (fun hn => hxQ (hn ▸ hx))
      have hcard : Nat.card Q < Nat.card N := by
        apply lt_of_not_ge
        intro hc
        exact hproper.ne (Subgroup.eq_of_le_of_card_ge hQN hc)
      have hm : Nat.card S - Nat.card N < n := by
        have hNS := N.card_le_card_group
        omega
      exact (F.centric_hom_count_modEq_normalizer p hS sat hQT hQ
        (F.toOrbit.obj ⟨T⟩)).trans
        (ih _ hm N rfl inf_le_right (F.centric_overgroup hQ hQN))
  exact main _ Q rfl hQT hQ

theorem top_fullyNormalized : F.FullyNormalized (⊤ : Subgroup S) := by
  intro Q e he
  change Nat.card (Subgroup.normalizer (Q : Set S)) ≤ Nat.card
    (Subgroup.normalizer ((⊤ : Subgroup S) : Set S))
  have ht : Subgroup.normalizer ((⊤ : Subgroup S) : Set S) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  rw [ht, Subgroup.card_top]
  exact (Subgroup.normalizer (Q : Set S)).card_le_card_group

theorem normalizerToOrbitAut_top_range :
    (F.normalizerToOrbitAut (⊤ : Subgroup S)).range = ⊥ := by
  apply le_antisymm _ bot_le
  rintro a ⟨n, rfl⟩
  exact F.subgroup_killed_by_normalizerAut ⊤ ⊤
    (x := ⟨n.val, n.property, Subgroup.mem_top _⟩) (Subgroup.mem_top _)

theorem top_orbit_aut_card_primeTo (p : ℕ) (sat : F.Saturated p) :
    ¬ p ∣ Nat.card (Aut (F.toOrbit.obj ⟨(⊤ : Subgroup S)⟩)) := by
  have h := F.normalizerToOrbitAut_range_index p sat ⊤ F.top_fullyNormalized
  simpa only [F.normalizerToOrbitAut_top_range, Subgroup.index_bot] using h

theorem centric_hom_top_card_primeTo (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {Q : Subgroup S} (hQ : F.IsCentric Q) :
    ¬ p ∣ Nat.card (F.toOrbit.obj ⟨Q⟩ ⟶ F.toOrbit.obj ⟨(⊤ : Subgroup S)⟩) := by
  have hc := F.centric_hom_count_modEq p hS sat (T := ⊤) le_top hQ
  intro hdiv
  exact F.top_orbit_aut_card_primeTo p sat
    (Nat.modEq_zero_iff_dvd.mp (hc.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdiv)))

/-- The top subgroup as an object of the actual centric orbit category. -/
def centricTopObject : F.CentricOrbit := ⟨F.toOrbit.obj ⟨⊤⟩, F.top_centric⟩

theorem centricOrbit_hom_top_card_primeTo (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (P : F.CentricOrbit) :
    ¬ p ∣ Nat.card (P ⟶ F.centricTopObject) := by
  let e : (P ⟶ F.centricTopObject) ≃ (P.obj ⟶ F.toOrbit.obj ⟨(⊤ : Subgroup S)⟩) :=
    { toFun f := f.hom
      invFun f := ⟨f⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr e]
  exact F.centric_hom_top_card_primeTo p hS sat P.property

end Sharpness.FusionSystem
