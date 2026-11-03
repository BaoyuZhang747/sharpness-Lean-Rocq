import Sharpness.CentricChainConjugacy
import Sharpness.FusionIsoRestriction

/-! Restrict actual fusion conjugacies to actual subchains. This proves
transitivity of the chain-to-conjugate-subchain relation directly from
the fusion axioms and supplies the relation used by the quotient category. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricChain
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}

def Conjugacy.restrictSubchain {σ τ : F.CentricChain} (c : Conjugacy σ τ) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) :
    Conjugacy (σ.subchain m e) (τ.subchain m (e.trans c.indices.toOrderEmbedding)) where
  indices := OrderIso.refl _
  topIso := F.restrictRawIso (σ.subgroup_mono (Fin.le_last _))
    (τ.subgroup_mono (Fin.le_last _)) c.topIso (c.maps (e (Fin.last m)))
  maps i x := c.maps (e i) ⟨x.val, σ.subgroup_mono (Fin.le_last _) x.property⟩

def IsSubconjugate (σ τ : F.CentricChain) : Prop :=
  ∃ (m : ℕ) (e : Fin (m + 1) ↪o Fin (σ.length + 1)), Conjugate (σ.subchain m e) τ

namespace IsSubconjugate
variable {σ τ υ : F.CentricChain}

theorem refl (σ : F.CentricChain) : IsSubconjugate σ σ := by
  refine ⟨σ.length, (OrderIso.refl _).toOrderEmbedding, ?_⟩
  rw [σ.subchain_refl]
  exact ⟨Conjugacy.refl σ⟩

theorem of_conjugate (c : Conjugate σ τ) : IsSubconjugate σ τ := by
  refine ⟨σ.length, (OrderIso.refl _).toOrderEmbedding, ?_⟩
  rw [σ.subchain_refl]
  exact c

theorem trans (h : IsSubconjugate σ τ) (k : IsSubconjugate τ υ) :
    IsSubconjugate σ υ := by
  obtain ⟨m, e, ⟨c⟩⟩ := h
  obtain ⟨n, d, ⟨b⟩⟩ := k
  refine ⟨n, (d.trans c.indices.symm.toOrderEmbedding).trans e, ?_⟩
  exact ⟨(c.symm.restrictSubchain n d).symm.trans b⟩

theorem congr {σ' τ' : F.CentricChain} (c : Conjugate σ σ') (d : Conjugate τ τ') :
    IsSubconjugate σ τ ↔ IsSubconjugate σ' τ' := by
  obtain ⟨c⟩ := c
  obtain ⟨d⟩ := d
  constructor
  · intro h
    exact (of_conjugate ⟨c.symm⟩).trans (h.trans (of_conjugate ⟨d⟩))
  · intro h
    exact (of_conjugate ⟨c⟩).trans (h.trans (of_conjugate ⟨d.symm⟩))

theorem length_le (h : IsSubconjugate σ τ) : τ.length ≤ σ.length := by
  obtain ⟨m, e, ⟨c⟩⟩ := h
  have hc : m = τ.length := c.length_eq
  have he := Fintype.card_le_of_injective e e.injective
  simp only [Fintype.card_fin] at he
  omega

end IsSubconjugate
end Sharpness.FusionSystem.CentricChain
