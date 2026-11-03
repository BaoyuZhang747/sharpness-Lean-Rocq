import Sharpness.Unconditional.NormalizerSubdivisionConjugacy

/-! Uniqueness of the subchain selected by a subdivision morphism,
and the free transitive target chain-automorphism action on its hom set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

theorem normalizer_chain_card_strict (σ : F.CentricChain) :
    StrictMono (fun i => Nat.card (σ.subgroup i)) := by
  intro i j hij
  apply lt_of_not_ge
  intro hcard
  exact (σ.subgroup_strict hij).ne
    (Subgroup.eq_of_le_of_card_ge (σ.subgroup_mono hij.le) hcard)

theorem normalizerSubdivision_indices_unique {σ τ : L.NormalizerSubdivision}
    (f g : σ ⟶ τ) : f.indices = g.indices := by
  have card_eq (h : σ ⟶ τ) (i : Fin (τ.chain.length + 1)) :
      Nat.card (σ.chain.subgroup (h.indices i)) = Nat.card (τ.chain.subgroup i) :=
    le_antisymm (F.order_mono (L.projection.map (h.component i).hom))
      (F.order_mono (L.projection.map (h.component i).inv))
  apply DFunLike.ext
  intro i
  apply (normalizer_chain_card_strict σ.chain).injective
  exact (card_eq f i).trans (card_eq g i).symm

theorem normalizerSubdivision_post_injective {σ τ : L.NormalizerSubdivision} (f : σ ⟶ τ) :
    Function.Injective (fun a : L.ChainAut τ.chain =>
      f ≫ L.normalizerSubdivisionAutHom τ.chain a) := by
  intro a b hab
  apply Subtype.ext
  funext i
  apply Iso.ext
  have hh : HEq (f ≫ L.normalizerSubdivisionAutHom τ.chain a).component
      (f ≫ L.normalizerSubdivisionAutHom τ.chain b).component :=
    congr_arg_heq (fun k : σ ⟶ τ => k.component) hab
  have h := congrArg (fun k => (k i).hom) (eq_of_heq hh)
  change (f.component i).hom ≫ (a.val i).hom = (f.component i).hom ≫ (b.val i).hom at h
  exact (cancel_epi (f.component i).hom).mp h

theorem normalizerSubdivision_hom_torsor {σ τ : L.NormalizerSubdivision} (f g : σ ⟶ τ) :
    ∃! a : L.ChainAut τ.chain, f ≫ L.normalizerSubdivisionAutHom τ.chain a = g := by
  have hi := L.normalizerSubdivision_indices_unique f g
  rcases f with ⟨e, a, ha⟩
  rcases g with ⟨e', b, hb⟩
  change e = e' at hi
  subst e'
  let d : L.ChainAut τ.chain :=
    ⟨fun i => (a i).symm.trans (b i), by
      intro i j hij
      change ((a i).inv ≫ (b i).hom) ≫ L.chainInclusion τ.chain hij =
        L.chainInclusion τ.chain hij ≫ ((a j).inv ≫ (b j).hom)
      apply (cancel_epi (a i).hom).mp
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Category.assoc, ha i j hij, Category.assoc, Iso.hom_inv_id_assoc]
      exact hb i j hij⟩
  have hd : (⟨e, a, ha⟩ : σ ⟶ τ) ≫ L.normalizerSubdivisionAutHom τ.chain d =
      (⟨e, b, hb⟩ : σ ⟶ τ) := by
    apply NormalizerSubdivisionHom.ext
    · rfl
    · apply heq_of_eq
      funext i
      apply Iso.ext
      change (a i).hom ≫ ((a i).inv ≫ (b i).hom) = (b i).hom
      exact Iso.hom_inv_id_assoc _ _
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  exact L.normalizerSubdivision_post_injective _ (hd'.trans hd.symm)

end Sharpness.FusionSystem.CentricLinkingSystem
