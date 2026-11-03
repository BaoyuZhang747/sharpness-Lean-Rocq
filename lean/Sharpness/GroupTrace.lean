import Sharpness.Trace

/-! The normalizer-trace cancellation, with an actual finite group and
its actual representation kernel and quotient cosets. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
open scoped BigOperators

theorem group_trace_zero_of_kernel (p : ℕ) [Fact p.Prime]
    {k : Type u} [Field k] [CharP k p]
    {G : Type v} [Group G] [Finite G] (pGroup : IsPGroup p G)
    {V : Type w} [AddCommGroup V] [Module k V]
    (ρ : G →* Module.End k V) (a : G) (ha : a ≠ 1) (hρ : ρ a = 1) (x : V) :
    letI : Fintype G := Fintype.ofFinite G
    (∑ g : G, ρ g x) = 0 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let K := ρ.ker
  haveI : Nontrivial K := ⟨⟨⟨a, hρ⟩, 1, fun h => ha (congrArg Subtype.val h)⟩⟩
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (G ⧸ K) := Fintype.ofFinite _
  have hpK : p ∣ Fintype.card K := by
    rcases (pGroup.to_subgroup K).card_eq_or_dvd with he | hd
    · exact (Finite.one_lt_card.ne' he).elim
    · simpa only [Nat.card_eq_fintype_card] using hd
  let e : G ≃ (G ⧸ K) × K := Subgroup.groupEquivQuotientProdSubgroup
  let qρ : G ⧸ K →* Module.End k V := QuotientGroup.lift K ρ (le_refl _)
  apply trace_zero_in_characteristic_p (R := k) p e (fun g => ρ g x)
    (fun q => qρ q x) _ hpK
  intro g
  have he : (e g).1 = QuotientGroup.mk g := rfl
  rw [he]
  rfl

end Sharpness
