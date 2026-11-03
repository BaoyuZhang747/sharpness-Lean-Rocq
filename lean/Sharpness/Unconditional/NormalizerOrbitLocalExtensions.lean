import Sharpness.Unconditional.NormalizerOrbitExtensionJoins
import Mathlib.Order.WellFounded

/-! The same-chain fibre has the literal normalizer-extension condition.
There is no nonidentity increasing self-embedding of a finite ordinal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

theorem normalizerChainExtension_self_iff_join {P Q : Subgroup S}
    (σ : F.CentricChain) (f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩) :
    Nonempty (F.NormalizerChainExtension σ σ f) ↔
      ∃ g : (⟨P ⊔ σ.topSubgroup⟩ : F.Object) ⟶ ⟨Q ⊔ σ.topSubgroup⟩,
        (∀ x : P, (g.val ⟨x.val,Subgroup.mem_sup_left x.property⟩).val = (f.val x).val) ∧
        (∀ i : Fin (σ.length + 1),
          (fun x : (P ⊔ σ.topSubgroup : Subgroup S) => (g.val x).val) ''
            {x | x.val ∈ σ.subgroup i} = (σ.subgroup i : Set S)) := by
  rw [F.normalizerChainExtension_iff_join]
  constructor
  · rintro ⟨e,g,hP,hC⟩
    have he : e = (OrderIso.refl _).toOrderEmbedding := by
      ext i
      exact le_antisymm (e.strictMono.le_id i) (e.strictMono.id_le i)
    subst e
    exact ⟨g,hP,hC⟩
  · rintro ⟨g,hP,hC⟩
    exact ⟨(OrderIso.refl _).toOrderEmbedding,g,hP,hC⟩

/-- The same statement in the top-first join order used for local normalizers. -/
theorem normalizerChainExtension_self_iff_topJoin {P Q : Subgroup S}
    (σ : F.CentricChain) (f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩) :
    Nonempty (F.NormalizerChainExtension σ σ f) ↔
      ∃ g : (⟨σ.topSubgroup ⊔ P⟩ : F.Object) ⟶ ⟨σ.topSubgroup ⊔ Q⟩,
        (∀ x : P, (g.val ⟨x.val,Subgroup.mem_sup_right x.property⟩).val = (f.val x).val) ∧
        (∀ i : Fin (σ.length + 1),
          (fun x : (σ.topSubgroup ⊔ P : Subgroup S) => (g.val x).val) ''
            {x | x.val ∈ σ.subgroup i} = (σ.subgroup i : Set S)) := by
  let J (D E : Subgroup S) : Prop :=
    ∃ (hPD : P ≤ D) (g : (⟨D⟩ : F.Object) ⟶ ⟨E⟩),
      (∀ x : P, (g.val ⟨x.val,hPD x.property⟩).val = (f.val x).val) ∧
      (∀ i : Fin (σ.length + 1),
        (fun x : D => (g.val x).val) '' {x | x.val ∈ σ.subgroup i} = (σ.subgroup i : Set S))
  have h : Nonempty (F.NormalizerChainExtension σ σ f) ↔
      J (P ⊔ σ.topSubgroup) (Q ⊔ σ.topSubgroup) := by
    rw [F.normalizerChainExtension_self_iff_join]
    constructor
    · rintro ⟨g,hP,hC⟩
      exact ⟨le_sup_left,g,hP,hC⟩
    · rintro ⟨hPD,g,hP,hC⟩
      exact ⟨g,hP,hC⟩
  rw [sup_comm P σ.topSubgroup,sup_comm Q σ.topSubgroup] at h
  constructor
  · intro ha
    obtain ⟨hPD,g,hP,hC⟩ := h.mp ha
    exact ⟨g,hP,hC⟩
  · rintro ⟨g,hP,hC⟩
    exact h.mpr ⟨le_sup_right,g,hP,hC⟩

end Sharpness.FusionSystem
