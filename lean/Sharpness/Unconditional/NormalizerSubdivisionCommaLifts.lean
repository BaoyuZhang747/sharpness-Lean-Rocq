import Sharpness.Unconditional.NormalizerSubdivisionConjugacy

/-! Actual linking-isomorphism lifts and compatible chain ladders for
the normalizer comma comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

omit [Finite S] in
theorem normalizer_exists_linkingIso {P Q : L.Object}
    (e : L.projection.obj P ≅ L.projection.obj Q) :
    ∃ a : P ≅ Q, L.projection.map a.hom = e.hom := by
  obtain ⟨f, hf⟩ := L.projection_surjective P Q e.hom
  obtain ⟨g, hg⟩ := L.projection_surjective Q P e.inv
  have hp : L.projection.map (𝟙 P) = L.projection.map (f ≫ g) := by
    rw [L.projection.map_id, L.projection.map_comp, hf, hg, e.hom_inv_id]
  obtain ⟨z, hz, _⟩ := (L.central_fiber (𝟙 P) (f ≫ g)).mp hp
  have hz' : f ≫ g = (L.distinguished P z.val).hom := by
    simpa only [Category.comp_id] using hz.symm
  let g' : Q ⟶ P := g ≫ (L.distinguished P z.val).inv
  have hfg : f ≫ g' = 𝟙 P := by
    change f ≫ (g ≫ (L.distinguished P z.val).inv) = _
    rw [← Category.assoc, hz', Iso.hom_inv_id]
  have hgf : g' ≫ f = 𝟙 Q := by
    apply L.cancel_right _ _ g'
    rw [Category.assoc, hfg, Category.comp_id, Category.id_comp]
  exact ⟨⟨f, g', hfg, hgf⟩, hf⟩

def normalizerLinkingIsoLift {P Q : L.Object}
    (e : L.projection.obj P ≅ L.projection.obj Q) : P ≅ Q :=
  Classical.choose (L.normalizer_exists_linkingIso e)

omit [Finite S] in
theorem normalizerLinkingIsoLift_projection {P Q : L.Object}
    (e : L.projection.obj P ≅ L.projection.obj Q) :
    L.projection.map (L.normalizerLinkingIsoLift e).hom = e.hom :=
  Classical.choose_spec (L.normalizer_exists_linkingIso e)

theorem normalizer_exists_chain_ladder (σ τ : F.CentricChain)
    (c : CentricChain.Conjugacy σ τ) :
    ∃ a : ∀ i : Fin (σ.length + 1), σ.linkingObject L i ≅ τ.linkingObject L (c.indices i),
      ∀ (i j : Fin (σ.length + 1)) (h : i ≤ j),
        (a i).hom ≫ L.chainInclusion τ (c.indices.monotone h) =
          L.chainInclusion σ h ≫ (a j).hom := by
  let t := L.normalizerLinkingIsoLift c.topIso
  have ht : L.projection.map t.hom = c.topIso.hom := L.normalizerLinkingIsoLift_projection _
  have exists_component (i : Fin (σ.length + 1)) :
      ∃ a : σ.linkingObject L i ≅ τ.linkingObject L (c.indices i),
        a.hom ≫ L.chainInclusion τ (Fin.le_last (c.indices i)) =
          L.chainInclusion σ (Fin.le_last i) ≫ t.hom := by
    let e := F.restrictRawIso (σ.subgroup_mono (Fin.le_last i))
      (τ.subgroup_mono (Fin.le_last (c.indices i))) c.topIso (c.maps i)
    let a := L.normalizerLinkingIsoLift e
    have hp : L.projection.map (a.hom ≫ L.chainInclusion τ (Fin.le_last (c.indices i))) =
        L.projection.map (L.chainInclusion σ (Fin.le_last i) ≫ t.hom) := by
      rw [L.projection.map_comp, L.projection.map_comp,
        L.normalizerLinkingIsoLift_projection, ht]
      change e.hom ≫ L.projection.map (L.inclusionLift _) =
        L.projection.map (L.inclusionLift _) ≫ c.topIso.hom
      rw [L.projection_inclusionLift, L.projection_inclusionLift]
      apply Subtype.ext
      apply MonoidHom.ext
      intro x
      apply Subtype.ext
      rfl
    obtain ⟨z, hz, _⟩ := (L.central_fiber
      (a.hom ≫ L.chainInclusion τ (Fin.le_last (c.indices i)))
      (L.chainInclusion σ (Fin.le_last i) ≫ t.hom)).mp hp
    refine ⟨(L.distinguished (σ.linkingObject L i) z.val).trans a, ?_⟩
    exact (Category.assoc _ _ _).trans hz
  choose a ha using exists_component
  refine ⟨a, ?_⟩
  intro i j hij
  apply L.cancel_right _ _ (L.chainInclusion τ (Fin.le_last (c.indices j)))
  calc
    ((a i).hom ≫ L.chainInclusion τ (c.indices.monotone hij)) ≫
        L.chainInclusion τ (Fin.le_last (c.indices j)) =
      (a i).hom ≫ L.chainInclusion τ (Fin.le_last (c.indices i)) := by
        rw [Category.assoc, L.chainInclusion_comp]
    _ = L.chainInclusion σ (Fin.le_last i) ≫ t.hom := ha i
    _ = (L.chainInclusion σ hij ≫ L.chainInclusion σ (Fin.le_last j)) ≫ t.hom := by
      rw [L.chainInclusion_comp]
    _ = L.chainInclusion σ hij ≫ ((a j).hom ≫
        L.chainInclusion τ (Fin.le_last (c.indices j))) := by
      rw [Category.assoc, ha j]
    _ = (L.chainInclusion σ hij ≫ (a j).hom) ≫
        L.chainInclusion τ (Fin.le_last (c.indices j)) := (Category.assoc _ _ _).symm

theorem normalizerSubdivision_exists_of_conjugacy (σ τ : F.CentricChain)
    (c : CentricChain.Conjugacy σ τ) :
    Nonempty (L.normalizerSubdivisionObj σ ⟶ L.normalizerSubdivisionObj τ) := by
  obtain ⟨a, ha⟩ := L.normalizer_exists_chain_ladder σ τ c
  rcases σ with ⟨n, s, hs⟩
  rcases τ with ⟨m, t, ht⟩
  have hnm : n = m := c.length_eq
  subst m
  rcases c with ⟨indices, topIso, maps⟩
  have hi : indices = OrderIso.refl _ := Subsingleton.elim _ _
  subst indices
  exact ⟨⟨(OrderIso.refl _).toOrderEmbedding, a, ha⟩⟩

theorem normalizerSubdivision_exists_of_subconjugate (σ τ : F.CentricChain)
    (h : CentricChain.IsSubconjugate σ τ) :
    Nonempty (L.normalizerSubdivisionObj σ ⟶ L.normalizerSubdivisionObj τ) := by
  obtain ⟨m, e, ⟨c⟩⟩ := h
  obtain ⟨f⟩ := L.normalizerSubdivision_exists_of_conjugacy (σ.subchain m e) τ c
  exact ⟨L.normalizerSubdivisionSubchainArrow σ m e ≫ f⟩

end Sharpness.FusionSystem.CentricLinkingSystem
