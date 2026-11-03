import Sharpness.Unconditional.NormalizerHigherLimitComparisonGroupsTransport
import Sharpness.Unconditional.NormalizerHigherLimitComparisonGroupsSylowEmbedding

/-! Actual conjugate centric chains with Sylow normalizer embedding.
The existing saturation proof supplies a Sylow transported K-automizer;
the chain transport below identifies that K with the transported chain's
actual stabilizer. No new local saturation theorem is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricChain
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}

omit [Finite S] in
theorem fusionStabilizer_eq_kTransport (σ τ : F.CentricChain)
    (e : σ.topSubgroup ≃* τ.topSubgroup) (he : F.IsHom e.toMonoidHom)
    (indices : Fin (σ.length + 1) ≃o Fin (τ.length + 1))
    (hm : ∀ (i : Fin (σ.length + 1)) (x : σ.topSubgroup),
      x.val ∈ σ.subgroup i ↔ (e x).val ∈ τ.subgroup (indices i)) :
    τ.fusionStabilizer = F.kTransport e he σ.fusionStabilizer := by
  let φ := F.alperinAutTransport e he
  ext a
  constructor
  · intro ha
    refine ⟨φ.symm a, ?_, φ.apply_symm_apply a⟩
    intro i x
    have h₀ := hm i x
    have h₁ := hm i ((φ.symm a).val x)
    have h₂ := ha (indices i) (e x)
    have hval : e ((φ.symm a).val x) = a.val (e x) := e.apply_symm_apply _
    rw [hval] at h₁
    exact h₀.trans (h₂.trans h₁.symm)
  · rintro ⟨b, hb, rfl⟩
    intro j y
    have h₀ := hm (indices.symm j) (e.symm y)
    have h₁ := hm (indices.symm j) (b.val (e.symm y))
    rw [indices.apply_symm_apply, e.apply_symm_apply] at h₀
    rw [indices.apply_symm_apply] at h₁
    exact h₀.symm.trans ((hb _ _).trans h₁)

/-- Every centric chain has an actual fusion-conjugate whose K-normalizer
automizer has prime-to-p index in its actual fusion stabilizer. -/
theorem exists_conjugate_sylow_automizer (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (σ : F.CentricChain) :
    ∃ τ : F.CentricChain, Conjugate σ τ ∧
      ¬ p ∣ (F.kNormalizerToAut τ.topSubgroup τ.fusionStabilizer).range.index := by
  obtain ⟨Q, e, he, _, hindex⟩ :=
    F.exists_fullyCentralized_kTransport_sylow p hS sat σ.topSubgroup σ.fusionStabilizer
  let τ := σ.transport e he
  have ht : τ.topSubgroup = Q := σ.transport_top e he
  let indices : Fin (σ.length + 1) ≃o Fin (τ.length + 1) := OrderIso.refl _
  have hm : ∀ (i : Fin (σ.length + 1)) (x : σ.topSubgroup),
      x.val ∈ σ.subgroup i ↔ (e x).val ∈ τ.subgroup (indices i) :=
    σ.transport_mem e he
  clear_value indices τ
  subst Q
  have hK := fusionStabilizer_eq_kTransport σ τ e he indices hm
  refine ⟨τ, ⟨⟨indices, F.isoOfMulEquiv e he, hm⟩⟩, ?_⟩
  rw [hK]
  exact hindex

end Sharpness.FusionSystem.CentricChain

namespace Sharpness.FusionSystem.CentricLinkingSystem
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

/-- Existence of a representative for which the literal simultaneous
normalizer embeds as a Sylow subgroup of the literal chain group. -/
theorem exists_conjugate_normalizer_sylow (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (σ : F.CentricChain) :
    ∃ τ : F.CentricChain, CentricChain.Conjugate σ τ ∧
      ∃ T : Sylow p (L.ChainAut τ), (T : Subgroup (L.ChainAut τ)) =
        (L.chainNormalizerToAut τ).range := by
  obtain ⟨τ, hc, hi⟩ := σ.exists_conjugate_sylow_automizer p hS sat
  let T := (L.chainNormalizerSylowCandidate_isPGroup p hS τ).toSylow (by
    rw [L.chainNormalizerSylowCandidate_index]
    exact hi)
  exact ⟨τ, hc, T, (L.chainNormalizerToAut_range τ).symm⟩

/-- A representative with the proved Sylow property for each actual
normalizer indexing object. The choice is independent of cohomology. -/
def normalizerSylowRepresentative (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (d : F.NormalizerCategory) : F.CentricChain :=
  Classical.choose (L.exists_conjugate_normalizer_sylow p hS sat (Quotient.out d))

theorem normalizerSylowRepresentative_class (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (d : F.NormalizerCategory) :
    F.normalizerClass (L.normalizerSylowRepresentative p hS sat d) = d := by
  have h := (Classical.choose_spec
    (L.exists_conjugate_normalizer_sylow p hS sat (Quotient.out d))).1
  exact ((F.normalizerClass_eq_iff _ _).mpr h).symm.trans (Quotient.out_eq d)

def normalizerRepresentativeSylow (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (d : F.NormalizerCategory) :
    Sylow p (L.ChainAut (L.normalizerSylowRepresentative p hS sat d)) :=
  Classical.choose (Classical.choose_spec
    (L.exists_conjugate_normalizer_sylow p hS sat (Quotient.out d))).2

theorem normalizerRepresentativeSylow_range (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (d : F.NormalizerCategory) :
    (L.normalizerRepresentativeSylow p hS sat d :
        Subgroup (L.ChainAut (L.normalizerSylowRepresentative p hS sat d))) =
      (L.chainNormalizerToAut (L.normalizerSylowRepresentative p hS sat d)).range :=
  Classical.choose_spec (Classical.choose_spec
    (L.exists_conjugate_normalizer_sylow p hS sat (Quotient.out d))).2

end Sharpness.FusionSystem.CentricLinkingSystem
