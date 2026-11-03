import Sharpness.Unconditional.CentricRigidity
import Sharpness.Unconditional.AlperinCentric
import Sharpness.Unconditional.FusionAtomicExtension

/-! Every morphism from a centric subgroup is epic in the orbit category.
The proof passes from normal-subgroup rigidity to arbitrary inclusions
using the normalizer condition in a finite p-group. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem centric_orbit_restriction_injective (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {Q R T : Subgroup S} (hQR : Q ≤ R) (hQ : F.IsCentric Q)
    (f g : (⟨R⟩ : F.Object) ⟶ ⟨T⟩)
    (hfg : F.toOrbit.map (F.inclusion hQR ≫ f) =
      F.toOrbit.map (F.inclusion hQR ≫ g)) :
    F.toOrbit.map f = F.toOrbit.map g := by
  have main : ∀ n : ℕ, ∀ (Q : Subgroup S), Nat.card S - Nat.card Q = n →
      ∀ (hQR : Q ≤ R), F.IsCentric Q →
      F.toOrbit.map (F.inclusion hQR ≫ f) =
        F.toOrbit.map (F.inclusion hQR ≫ g) → F.toOrbit.map f = F.toOrbit.map g := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Q hn hQR hQ heq
      by_cases h : Q = R
      · subst Q
        exact heq
      let N := Subgroup.normalizer (Q : Set S) ⊓ R
      have hQN : Q ≤ N := le_inf Subgroup.le_normalizer hQR
      have hNR : N ≤ R := inf_le_right
      have hproper : Q < N := by
        apply lt_of_le_of_ne hQN
        intro he
        have hsmall : Q.subgroupOf R ≠ ⊤ := by
          intro ht
          exact h (le_antisymm hQR (Subgroup.subgroupOf_eq_top.mp ht))
        have hlt := proper_subgroup_lt_normalizer p (hS.to_subgroup R) hsmall
        obtain ⟨x, hxN, hxQ⟩ := SetLike.not_le_iff_exists.mp (not_le_of_gt hlt)
        have hxn : x.val ∈ Subgroup.normalizer (Q : Set S) := by
          rw [← Subgroup.subgroupOf_normalizer_eq hQR] at hxN
          exact hxN
        exact hxQ (he ▸ show x.val ∈ N from ⟨hxn, x.property⟩)
      letI : (Q.subgroupOf N).Normal := Subgroup.normal_subgroupOf_of_le_normalizer inf_le_left
      have hres : F.toOrbit.map (F.inclusion hNR ≫ f) =
          F.toOrbit.map (F.inclusion hNR ≫ g) := by
        apply F.centric_normal_orbit_restriction_injective p hS sat hQN hQ
        exact heq
      have hcard : Nat.card Q < Nat.card N := by
        apply lt_of_not_ge
        intro hc
        exact hproper.ne (Subgroup.eq_of_le_of_card_ge hQN hc)
      have hmeasure : Nat.card S - Nat.card N < n := by
        have hNS := N.card_le_card_group
        omega
      exact ih _ hmeasure N rfl hNR (F.centric_overgroup hQ hQN) hres
  exact main _ Q rfl hQR hQ hfg

/-- Puig's centric epimorphism property for the actual orbit category. -/
theorem centric_orbit_epi (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {P Q : F.Orbit} (f : P ⟶ Q) (hP : F.IsCentric P.as.subgroup) : Epi f := by
  rcases P with ⟨P⟩
  rcases Q with ⟨Q⟩
  obtain ⟨f, rfl⟩ := F.toOrbit.map_surjective f
  constructor
  intro T g h heq
  rcases T with ⟨T⟩
  obtain ⟨g, rfl⟩ := F.toOrbit.map_surjective g
  obtain ⟨h, rfl⟩ := F.toOrbit.map_surjective h
  have hL : F.IsCentric (F.imageSubgroup f) :=
    F.isoSystem.centricIn_of_iso (F.atomicImageEquiv f) (F.atomicImageEquiv_allowed f) hP
  apply F.centric_orbit_restriction_injective p hS sat (F.image_le f) hL g h
  apply (cancel_epi (F.toOrbit.map (F.imageIso f).hom)).mp
  simpa only [← F.toOrbit.map_comp, ← Category.assoc, imageIso, image_factorization] using heq

/-- Every morphism in the centric orbit category is an epimorphism. -/
theorem centric_epi (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {P Q : F.CentricOrbit} (f : P ⟶ Q) : Epi f := by
  letI := F.centric_orbit_epi p hS sat f.hom P.property
  constructor
  intro T g h heq
  apply InducedCategory.hom_ext
  apply (cancel_epi f.hom).mp
  exact congrArg (fun a : P ⟶ T => a.hom) heq

end Sharpness.FusionSystem
