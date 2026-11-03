import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocal

/-! Actual conjugation by a compatible linking-chain automorphism is
realized by an ambient fusion extension over the chain top. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

theorem chainAut_induces_normalizerExtension (p : ℕ) (sat : F.Saturated p)
    (σ : F.CentricChain) {P Q : Subgroup S}
    (hP : P ≤ σ.normalizerSubgroup) (hQ : Q ≤ σ.normalizerSubgroup)
    (f : P →* Q) (g : L.ChainAut σ)
    (hg : ∀ x : P, L.chainNormalizerToAut σ ⟨(f x).val, hQ (f x).property⟩ =
      g * L.chainNormalizerToAut σ ⟨x.val, hP x.property⟩ * g⁻¹) :
    σ.NormalizerExtension f := by
  let Z := σ.linkingObject L (Fin.last σ.length)
  let U := L.normalizerJoinObject σ P
  let V := L.normalizerJoinObject σ Q
  let a : Aut Z := L.chainAutProjection σ (Fin.last σ.length) g
  have hZU : Z.as.val ≤ U.as.val := le_sup_left
  have hZV : Z.as.val ≤ V.as.val := le_sup_left
  have hUN : U.as.val ≤ Subgroup.normalizer (Z.as.val : Set S) :=
    σ.normalizerJoin_le_normalizer hP
  have hVN : V.as.val ≤ Subgroup.normalizer (Z.as.val : Set S) :=
    σ.normalizerJoin_le_normalizer hQ
  have hconj (x : P) : L.normalizerToLinkingAut Z
      ⟨(f x).val, (σ.mem_normalizerSubgroup _).mp (hQ (f x).property) (Fin.last σ.length)⟩ =
      a * L.normalizerToLinkingAut Z
        ⟨x.val, (σ.mem_normalizerSubgroup _).mp (hP x.property) (Fin.last σ.length)⟩ * a⁻¹ := by
    have hh := congrArg (L.chainAutProjection σ (Fin.last σ.length)) (hg x)
    rw [map_mul, map_mul, map_inv] at hh
    exact hh
  have hPD : P ≤ L.linkingNormalizerConjugationDomain Z V hVN a := by
    intro x hx
    rw [L.mem_linkingNormalizerConjugationDomain]
    refine ⟨(σ.mem_normalizerSubgroup _).mp (hP hx) (Fin.last σ.length),
      ⟨(f ⟨x, hx⟩).val, Subgroup.mem_sup_right (f ⟨x, hx⟩).property⟩, ?_⟩
    exact hconj ⟨x, hx⟩
  have hUD : U.as.val ≤ L.linkingNormalizerConjugationDomain Z V hVN a :=
    sup_le (L.le_linkingNormalizerConjugationDomain hZV hVN a) hPD
  have hw : ∀ x : U.as.val, ∃ y : V.as.val,
      L.normalizerToLinkingAut Z ⟨y.val, hVN y.property⟩ =
        a * L.normalizerToLinkingAut Z ⟨x.val, hUN x.property⟩ * a⁻¹ := by
    intro x
    obtain ⟨_, y, hy⟩ := (L.mem_linkingNormalizerConjugationDomain Z V hVN a x.val).mp
      (hUD x.property)
    exact ⟨y, hy⟩
  obtain ⟨b, hb⟩ := L.exists_linking_normalizer_extension p sat hZU hZV hUN hVN a hw
  refine ⟨L.chainFusionProjection σ g, (L.projection.map b).val,
    (L.projection.map b).property, ?_, ?_⟩
  · intro x
    have he := congrArg (fun t => L.projection.map t) hb
    rw [L.projection.map_comp, L.projection.map_comp,
      L.projection_inclusionLift, L.projection_inclusionLift] at he
    exact congrArg (fun t => (t.val x).val) he
  · intro x
    have he := L.linking_normalizer_extension_conjugation hZU hZV hUN hVN a b hb
      (⟨x.val, Subgroup.mem_sup_right x.property⟩ : U.as.val)
    have hh := he.trans (hconj x).symm
    have hn := L.normalizerToLinkingAut_injective Z hh
    exact congrArg (fun t : Subgroup.normalizer (Z.as.val : Set S) => t.val) hn

/-- The extension definition agrees exactly with conjugation in the actual
finite linking-chain automorphism group. No local saturation is assumed. -/
theorem normalizerExtension_iff_chainAut (p : ℕ) (sat : F.Saturated p)
    (σ : F.CentricChain) {P Q : Subgroup S}
    (hP : P ≤ σ.normalizerSubgroup) (hQ : Q ≤ σ.normalizerSubgroup) (f : P →* Q) :
    σ.NormalizerExtension f ↔ ∃ g : L.ChainAut σ, ∀ x : P,
      L.chainNormalizerToAut σ ⟨(f x).val, hQ (f x).property⟩ =
        g * L.chainNormalizerToAut σ ⟨x.val, hP x.property⟩ * g⁻¹ :=
  ⟨L.normalizerExtension_induced_by_chainAut σ hP hQ f,
    fun ⟨g, hg⟩ => L.chainAut_induces_normalizerExtension p sat σ hP hQ f g hg⟩

end Sharpness.FusionSystem.CentricLinkingSystem

