import Sharpness.Unconditional.NormalizerSubdivisionComparison

/-! The actual natural isomorphism for conjugate chains. Its component
retains the specified linking isomorphisms instead of identifying the
two comparison functors strictly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def normalizerSubdivisionComparison_conjugacy (σ τ : F.CentricChain)
    (c : CentricChain.Conjugacy σ τ)
    (a : ∀ i : Fin (σ.length + 1), σ.linkingObject L i ≅ τ.linkingObject L (c.indices i))
    (ha : ∀ (i j : Fin (σ.length + 1)) (h : i ≤ j),
      (a i).hom ≫ L.chainInclusion τ (c.indices.monotone h) =
        L.chainInclusion σ h ≫ (a j).hom)
    (φ : L.ChainAut σ ≃* L.ChainAut τ)
    (hφ : ∀ (g : L.ChainAut σ) (i : Fin (σ.length + 1)),
      ((φ g).val (c.indices i)).hom = (a i).inv ≫ (g.val i).hom ≫ (a i).hom) :
    L.normalizerSubdivisionChainComparison σ ⋙ CostructuredArrow.map
      (eqToHom ((F.normalizerClass_eq_iff σ τ).mpr ⟨c⟩)) ≅
      φ.toMonoidHom.toFunctor ⋙ L.normalizerSubdivisionChainComparison τ := by
  rcases σ with ⟨n, s, hs⟩
  rcases τ with ⟨m, t, ht⟩
  have hnm : n = m := c.length_eq
  subst m
  rcases c with ⟨indices, topIso, maps⟩
  have hi : indices = OrderIso.refl _ := Subsingleton.elim _ _
  subst indices
  let σ : F.CentricChain := ⟨n, s, hs⟩
  let τ : F.CentricChain := ⟨n, t, ht⟩
  let e : L.normalizerSubdivisionObj σ ≅ L.normalizerSubdivisionObj τ :=
    { hom :=
        { indices := (OrderIso.refl _).toOrderEmbedding
          component := a
          commutes := ha }
      inv :=
        { indices := (OrderIso.refl _).toOrderEmbedding
          component i := (a i).symm
          commutes i j h := by
            change (a i).inv ≫ L.chainInclusion σ h =
              L.chainInclusion τ h ≫ (a j).inv
            apply (cancel_epi (a i).hom).mp
            apply (cancel_mono (a j).hom).mp
            simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
              Category.comp_id] using (ha i j h).symm }
      hom_inv_id := by
        apply NormalizerSubdivisionHom.ext
        · rfl
        · apply heq_of_eq
          funext i
          apply Iso.ext
          exact (a i).hom_inv_id
      inv_hom_id := by
        apply NormalizerSubdivisionHom.ext
        · rfl
        · apply heq_of_eq
          funext i
          apply Iso.ext
          exact (a i).inv_hom_id }
  refine NatIso.ofComponents
    (fun _ => CostructuredArrow.isoMk e (by apply Subsingleton.elim)) ?_
  intro X Y g
  apply CostructuredArrow.hom_ext
  apply NormalizerSubdivisionHom.ext
  · rfl
  · apply heq_of_eq
    funext i
    apply Iso.ext
    change (g.val i).hom ≫ (a i).hom = (a i).hom ≫ ((φ g).val i).hom
    have hg : ((φ g).val i).hom = (a i).inv ≫ (g.val i).hom ≫ (a i).hom := hφ g i
    rw [hg]
    rw [Iso.hom_inv_id_assoc]

omit [Finite S] in
theorem normalizerConjugacy_indices_zero {σ τ : F.CentricChain}
    (c : CentricChain.Conjugacy σ τ) : c.indices 0 = 0 := by
  apply le_antisymm
  · have h := c.indices.monotone (Fin.zero_le (c.indices.symm 0))
    simpa only [c.indices.apply_symm_apply] using h
  · exact Fin.zero_le _

theorem normalizerSubdivisionComparison_conjugacy_component (σ τ : F.CentricChain)
    (c : CentricChain.Conjugacy σ τ)
    (a : ∀ i : Fin (σ.length + 1), σ.linkingObject L i ≅ τ.linkingObject L (c.indices i))
    (ha : ∀ (i j : Fin (σ.length + 1)) (h : i ≤ j),
      (a i).hom ≫ L.chainInclusion τ (c.indices.monotone h) =
        L.chainInclusion σ h ≫ (a j).hom)
    (φ : L.ChainAut σ ≃* L.ChainAut τ)
    (hφ : ∀ (g : L.ChainAut σ) (i : Fin (σ.length + 1)),
      ((φ g).val (c.indices i)).hom = (a i).inv ≫ (g.val i).hom ≫ (a i).hom) :
    L.normalizerSubdivisionEvaluation.map
      (((L.normalizerSubdivisionComparison_conjugacy σ τ c a ha φ hφ).hom.app
        (SingleObj.star (L.ChainAut σ))).left) =
      (a 0).hom ≫ eqToHom (congrArg (τ.linkingObject L) (normalizerConjugacy_indices_zero c)) := by
  rcases σ with ⟨n, s, hs⟩
  rcases τ with ⟨m, t, ht⟩
  have hnm : n = m := c.length_eq
  subst m
  rcases c with ⟨indices, topIso, maps⟩
  have hi : indices = OrderIso.refl _ := Subsingleton.elim _ _
  subst indices
  change L.chainInclusion (⟨n, s, hs⟩ : F.CentricChain) (le_refl 0) ≫ (a 0).hom =
    (a 0).hom ≫ 𝟙 _
  simp only [L.chainInclusion_refl, Category.id_comp, Category.comp_id]

end Sharpness.FusionSystem.CentricLinkingSystem
