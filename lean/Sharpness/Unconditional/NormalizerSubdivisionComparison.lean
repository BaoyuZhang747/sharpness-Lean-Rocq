import Sharpness.Unconditional.NormalizerSubdivisionProjection
import Sharpness.LinkingSubgroupDiagram

/-! Actual chain-automorphism inclusions into the normalizer comma
model, with strict evaluation factorization and a natural subchain
square. The subchain square is not a strict equality of functors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def normalizerSubdivisionAutHom (σ : F.CentricChain) :
    L.ChainAut σ →* End (L.normalizerSubdivisionObj σ) where
  toFun a :=
    { indices := (OrderIso.refl _).toOrderEmbedding
      component i := a.val i
      commutes := a.property }
  map_one' := by
    apply NormalizerSubdivisionHom.ext
    · rfl
    · rfl
  map_mul' a b := by
    apply NormalizerSubdivisionHom.ext
    · rfl
    · rfl

def normalizerSubdivisionAutFunctor (σ : F.CentricChain) :
    SingleObj (L.ChainAut σ) ⥤ L.NormalizerSubdivision :=
  SingleObj.functor (L.normalizerSubdivisionAutHom σ)

def normalizerSubdivisionChainComparison (σ : F.CentricChain) :
    SingleObj (L.ChainAut σ) ⥤
      CostructuredArrow L.normalizerSubdivisionProjection (F.normalizerClass σ) :=
  (L.normalizerSubdivisionAutFunctor σ).toCostructuredArrow L.normalizerSubdivisionProjection
    (F.normalizerClass σ) (fun _ => 𝟙 _) (by intros; apply Subsingleton.elim)

theorem normalizerSubdivisionComparison_factorization (σ : F.CentricChain) :
    L.normalizerSubdivisionChainComparison σ ⋙
      CostructuredArrow.proj L.normalizerSubdivisionProjection (F.normalizerClass σ) ⋙
        L.normalizerSubdivisionEvaluation = L.chainAutomorphismFunctor σ := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y a
  change L.chainInclusion σ (le_refl 0) ≫ (a.val 0).hom =
    𝟙 _ ≫ (a.val 0).hom ≫ 𝟙 _
  simp only [L.chainInclusion_refl, Category.id_comp, Category.comp_id]

def normalizerSubdivisionSubchainArrow (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) :
    L.normalizerSubdivisionObj σ ⟶ L.normalizerSubdivisionObj (σ.subchain m e) where
  indices := e
  component i := Iso.refl _
  commutes i j h := by
    change (𝟙 _) ≫ L.chainInclusion σ (e.monotone h) =
      L.chainInclusion σ (e.monotone h) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]

theorem normalizerSubdivisionSubchainArrow_evaluation (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) :
    L.normalizerSubdivisionEvaluation.map (L.normalizerSubdivisionSubchainArrow σ m e) =
      L.chainInclusion σ (Fin.zero_le (e 0)) :=
  Category.comp_id _

def normalizerSubdivisionComparison_subchain (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) :
    L.normalizerSubdivisionChainComparison σ ⋙
      CostructuredArrow.map (F.normalizerSubchainArrow σ m e) ⟶
      (L.chainAutRestriction σ m e).toFunctor ⋙
        L.normalizerSubdivisionChainComparison (σ.subchain m e) :=
  SingleObj.natTrans
    (CostructuredArrow.homMk (L.normalizerSubdivisionSubchainArrow σ m e)
      (by apply Subsingleton.elim)) (by
    intro a
    apply CostructuredArrow.hom_ext
    apply NormalizerSubdivisionHom.ext
    · rfl
    · apply heq_of_eq
      funext i
      apply Iso.ext
      change (a.val (e i)).hom ≫ 𝟙 _ = 𝟙 _ ≫ (a.val (e i)).hom
      rw [Category.comp_id, Category.id_comp])

theorem normalizerSubdivisionComparison_subchain_component (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) :
    L.normalizerSubdivisionEvaluation.map
      ((L.normalizerSubdivisionComparison_subchain σ m e).app
        (SingleObj.star (L.ChainAut σ))).left =
      L.chainInclusion σ (Fin.zero_le (e 0)) :=
  L.normalizerSubdivisionSubchainArrow_evaluation σ m e

end Sharpness.FusionSystem.CentricLinkingSystem
