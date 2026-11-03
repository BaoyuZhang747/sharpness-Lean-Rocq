import Sharpness.Unconditional.NormalizerOrbitProjectionCommaChainExtension
import Sharpness.Unconditional.NormalizerOrbitLocalCategory
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! Actual pointing of an object over a chain class toward a fixed Sylow
representative. The pointing is a genuine pair-category arrow and an
isomorphism on the acting centric subgroups. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}

omit [Finite S] in
theorem normalizer_map_mem_of_subgroup_image {N U V : Subgroup S}
    (f : N →* S) (hU : U ≤ N)
    (himage : f '' {x : N | x.val ∈ U} = (V : Set S))
    (x : N) (hx : x.val ∈ Subgroup.normalizer (U : Set S)) :
    f x ∈ Subgroup.normalizer (V : Set S) := by
  have heq : (U.subgroupOf N).map f = V := by
    apply SetLike.coe_injective
    exact himage
  rw [← heq]
  apply (U.subgroupOf N).le_normalizer_map
  refine ⟨x, ?_, rfl⟩
  rw [← Subgroup.subgroupOf_normalizer_eq hU]
  exact hx

theorem NormalizerOrbitPair.exists_pointing_of_selected_conjugacy
    (A : F.NormalizerOrbitPair) {σ : F.CentricChain} (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (A.chain.length + 1))
    (c : CentricChain.Conjugacy (A.chain.subchain m e) σ)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (hSylow : ¬ p ∣ (F.kNormalizerToAut σ.topSubgroup σ.fusionStabilizer).range.index) :
    ∃ (B : F.NormalizerOrbitAtChain σ) (u : A ⟶ B.obj),
      IsIso (F.normalizerOrbitPairForget.map u) := by
  let κ := A.chain.subchain m e
  obtain ⟨N, hTop, hNorm, f, himages⟩ := c.exists_normalizer_extension p hS sat hSylow
  have hPN : A.centric.obj.as.subgroup ≤ N := by
    intro x hx
    apply hNorm
    apply (κ.mem_normalizerSubgroup x).mpr
    intro i
    exact A.normalizes (e i) hx
  let g : A.centric.obj.as ⟶ (⟨⊤⟩ : F.Object) := F.inclusion hPN ≫ f
  have hQ : F.IsCentric (F.imageSubgroup g) := by
    let eg := F.alperinMulEquivOfIso (F.imageIso g)
    exact F.isoSystem.centricIn_of_iso eg (F.toImage g).property A.centric.property
  let B : F.NormalizerOrbitPair :=
    { centric := ⟨F.toOrbit.obj ⟨F.imageSubgroup g⟩, hQ⟩
      chain := σ
      normalizes := by
        intro j y hy
        obtain ⟨x, rfl⟩ := hy
        apply normalizer_map_mem_of_subgroup_image ((⊤ : Subgroup S).subtype.comp f.val)
          ((κ.subgroup_mono (Fin.le_last _)).trans hTop)
          (by
            change (fun x : N => (f.val x).val) ''
              {x : N | x.val ∈ κ.subgroup (c.indices.symm j)} = _
            simpa only [c.indices.apply_symm_apply] using himages (c.indices.symm j))
          ⟨x.val, hPN x.property⟩
        exact A.normalizes (e (c.indices.symm j)) x.property }
  have hlast : c.indices.symm (Fin.last σ.length) = Fin.last m := c.indices.symm.map_top
  let a : F.NormalizerChainExtension A.chain σ (F.toImage g) :=
    { indices := c.indices.symm.toOrderEmbedding.trans e
      carrier := N
      acting_le := hPN
      chain_le := by
        change A.chain.subgroup (e (c.indices.symm (Fin.last σ.length))) ≤ N
        rw [hlast]
        exact hTop
      extension := f
      onActing x := rfl
      images j := by
        change (fun x : N => (f.val x).val) ''
          {x : N | x.val ∈ κ.subgroup (c.indices.symm j)} = (σ.subgroup j : Set S)
        simpa only [c.indices.apply_symm_apply] using himages (c.indices.symm j) }
  let u : A ⟶ B := NormalizerOrbitPair.homMk (F.toImage g) a
  let eg : A.centric ≅ B.centric := ObjectProperty.isoMk _ (F.toOrbit.mapIso (F.imageIso g))
  exact ⟨⟨B, rfl⟩, u, eg.isIso_hom⟩

theorem NormalizerOrbitPair.exists_pointing_of_subconjugate
    (A : F.NormalizerOrbitPair) (σ : F.CentricChain)
    (h : CentricChain.IsSubconjugate A.chain σ)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (hSylow : ¬ p ∣ (F.kNormalizerToAut σ.topSubgroup σ.fusionStabilizer).range.index) :
    ∃ (B : F.NormalizerOrbitAtChain σ) (u : A ⟶ B.obj),
      IsIso (F.normalizerOrbitPairForget.map u) := by
  obtain ⟨m, e, ⟨c⟩⟩ := h
  exact A.exists_pointing_of_selected_conjugacy m e c p hS sat hSylow

namespace CentricLinkingSystem
variable (L : F.CentricLinkingSystem)

/-- Every actual p-comma object admits a pointing to the chosen literal Sylow
chain representative, and this pointing preserves the acting group up to isomorphism. -/
theorem exists_pointing_to_sylow_chain (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (d : F.NormalizerCategory)
    (X : CostructuredArrow F.normalizerOrbitPairProjection d) :
    ∃ (B : F.NormalizerOrbitAtChain (L.normalizerSylowRepresentative p hS sat d))
      (u : X.left ⟶ B.obj), IsIso (F.normalizerOrbitPairForget.map u) := by
  have hc : CentricChain.IsSubconjugate X.left.chain
      (L.normalizerSylowRepresentative p hS sat d) := by
    apply (F.normalizerClass_le_iff _ _).mp
    rw [L.normalizerSylowRepresentative_class p hS sat d]
    exact leOfHom X.hom
  exact X.left.exists_pointing_of_subconjugate _ hc p hS sat
    (L.normalizerRepresentative_automizer_sylow p hS sat d)

end CentricLinkingSystem
end Sharpness.FusionSystem
