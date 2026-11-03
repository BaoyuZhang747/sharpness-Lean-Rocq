import Sharpness.ChainAutomorphismFunctors
import Sharpness.NormalizerChainCategory

/-! The subdivision on actual strict centric subgroup chains with the
chosen coherent linking inclusions. An arrow selects a subchain of its
source and gives an isomorphism from that subchain to its target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

structure NormalizerSubdivision (_L : F.CentricLinkingSystem) where
  chain : F.CentricChain

structure NormalizerSubdivisionHom (σ τ : L.NormalizerSubdivision) where
  indices : Fin (τ.chain.length + 1) ↪o Fin (σ.chain.length + 1)
  component : ∀ i, σ.chain.linkingObject L (indices i) ≅ τ.chain.linkingObject L i
  commutes : ∀ (i j : Fin (τ.chain.length + 1)) (h : i ≤ j),
    (component i).hom ≫ L.chainInclusion τ.chain h =
      L.chainInclusion σ.chain (indices.monotone h) ≫ (component j).hom

namespace NormalizerSubdivisionHom
variable {L} {σ τ υ ω : L.NormalizerSubdivision}

theorem ext (f g : L.NormalizerSubdivisionHom σ τ) (hi : f.indices = g.indices)
    (hc : HEq f.component g.component) : f = g := by
  cases f
  cases g
  cases hi
  cases hc
  rfl

def id (σ : L.NormalizerSubdivision) : L.NormalizerSubdivisionHom σ σ where
  indices := (OrderIso.refl _).toOrderEmbedding
  component i := Iso.refl _
  commutes i j h := by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

def comp (f : L.NormalizerSubdivisionHom σ τ) (g : L.NormalizerSubdivisionHom τ υ) :
    L.NormalizerSubdivisionHom σ υ where
  indices := g.indices.trans f.indices
  component i := (f.component (g.indices i)).trans (g.component i)
  commutes i j h := by
    change ((f.component (g.indices i)).hom ≫ (g.component i).hom) ≫
      L.chainInclusion υ.chain h = _
    rw [Category.assoc, g.commutes i j h, ← Category.assoc,
      f.commutes (g.indices i) (g.indices j) (g.indices.monotone h), Category.assoc]
    rfl

end NormalizerSubdivisionHom

instance normalizerSubdivisionCategory : Category.{u} L.NormalizerSubdivision where
  Hom := L.NormalizerSubdivisionHom
  id := NormalizerSubdivisionHom.id
  comp := NormalizerSubdivisionHom.comp
  id_comp f := by
    apply NormalizerSubdivisionHom.ext
    · rfl
    apply heq_of_eq
    funext i
    apply Iso.ext
    exact Category.id_comp _
  comp_id f := by
    apply NormalizerSubdivisionHom.ext
    · rfl
    apply heq_of_eq
    funext i
    apply Iso.ext
    exact Category.comp_id _
  assoc f g h := by
    apply NormalizerSubdivisionHom.ext
    · rfl
    apply heq_of_eq
    funext i
    apply Iso.ext
    exact Category.assoc _ _ _

def normalizerSubdivisionObj (σ : F.CentricChain) : L.NormalizerSubdivision := ⟨σ⟩

/-- Evaluation at the first object, with the initial inclusion when
the selected subchain does not start at the first source object. -/
def normalizerSubdivisionEvaluation : L.NormalizerSubdivision ⥤ L.Object where
  obj σ := σ.chain.linkingObject L 0
  map {σ τ} f := L.chainInclusion σ.chain (Fin.zero_le (f.indices 0)) ≫ (f.component 0).hom
  map_id σ := by
    change L.chainInclusion σ.chain (le_refl 0) ≫ 𝟙 _ = 𝟙 _
    rw [L.chainInclusion_refl, Category.comp_id]
  map_comp {σ τ υ} f g := by
    change L.chainInclusion σ.chain (Fin.zero_le (f.indices (g.indices 0))) ≫
      ((f.component (g.indices 0)).hom ≫ (g.component 0).hom) =
      (L.chainInclusion σ.chain (Fin.zero_le (f.indices 0)) ≫ (f.component 0).hom) ≫
        (L.chainInclusion τ.chain (Fin.zero_le (g.indices 0)) ≫ (g.component 0).hom)
    have h := congrArg
      (fun t => L.chainInclusion σ.chain (Fin.zero_le (f.indices 0)) ≫ t ≫ (g.component 0).hom)
      (f.commutes 0 (g.indices 0) (Fin.zero_le _))
    simpa only [← Category.assoc, L.chainInclusion_comp] using h.symm

end Sharpness.FusionSystem.CentricLinkingSystem
