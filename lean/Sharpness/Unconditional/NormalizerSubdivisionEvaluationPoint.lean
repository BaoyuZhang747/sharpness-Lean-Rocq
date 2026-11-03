import Sharpness.Unconditional.NormalizerSubdivisionEvaluationCoreflection

/-! The actual terminal singleton in the coreflective pointed subcategory. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}

def CentricChain.singleton (P : F.CentricSubgroup) : F.CentricChain where
  length := 0
  entry _ := P
  strict := by
    intro i j hij
    change Fin 1 at i j
    exact ((ne_of_lt hij) (Subsingleton.elim i j)).elim

namespace CentricLinkingSystem
variable [Finite S] (L : F.CentricLinkingSystem)

def normalizerSingletonSelection (τ : F.CentricChain) (P : L.Object)
    (a : P ≅ τ.linkingObject L 0) :
    L.normalizerSubdivisionObj τ ⟶ L.normalizerSubdivisionObj (CentricChain.singleton P.as) where
  indices := OrderEmbedding.ofStrictMono (fun _ => 0) (by
    intro i j hij
    change Fin 1 at i j
    exact ((ne_of_lt hij) (Subsingleton.elim i j)).elim)
  component _ := a.symm
  commutes i j hij := by
    change a.inv ≫ L.inclusionLift (le_refl P.as.val) =
      L.inclusionLift (le_refl (τ.subgroup 0)) ≫ a.inv
    rw [L.inclusionLift_refl, L.inclusionLift_refl,
      Category.id_comp, Category.comp_id]

theorem normalizerSingletonSelection_evaluation (τ : F.CentricChain) (P : L.Object)
    (a : P ≅ τ.linkingObject L 0) :
    L.normalizerSubdivisionEvaluation.map (L.normalizerSingletonSelection τ P a) = a.inv := by
  change L.chainInclusion τ (le_refl 0) ≫ a.inv = _
  rw [L.chainInclusion_refl, Category.id_comp]

theorem normalizerSingletonSelection_unique (τ : F.CentricChain) (P : L.Object)
    (a : P ≅ τ.linkingObject L 0)
    (f : L.normalizerSubdivisionObj τ ⟶ L.normalizerSubdivisionObj (CentricChain.singleton P.as))
    (hf : a.hom ≫ L.normalizerSubdivisionEvaluation.map f = 𝟙 P) :
    f = L.normalizerSingletonSelection τ P a := by
  have hi := L.normalizerSubdivision_indices_unique f (L.normalizerSingletonSelection τ P a)
  rcases f with ⟨indices, component, commutes⟩
  change indices = (L.normalizerSingletonSelection τ P a).indices at hi
  subst indices
  apply NormalizerSubdivisionHom.ext
  · rfl
  apply heq_of_eq
  funext i
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  apply Iso.ext
  change (component 0).hom = a.inv
  apply (cancel_epi a.hom).mp
  change a.hom ≫ (L.chainInclusion τ (le_refl 0) ≫ (component 0).hom) = 𝟙 P at hf
  rw [L.chainInclusion_refl, Category.id_comp] at hf
  exact hf.trans a.hom_inv_id.symm

def normalizerEvaluationPoint (P : L.Object) : L.NormalizerEvaluationPointed P :=
  ⟨StructuredArrow.mk (Y := L.normalizerSubdivisionObj (CentricChain.singleton P.as))
    (𝟙 P), inferInstanceAs (IsIso (𝟙 P))⟩

def normalizerEvaluationPointArrow (P : L.Object) (X : L.NormalizerEvaluationPointed P) :
    X ⟶ L.normalizerEvaluationPoint P := by
  letI : IsIso X.obj.hom := X.property
  exact ObjectProperty.homMk (StructuredArrow.homMk
    (L.normalizerSingletonSelection X.obj.right.chain P (asIso X.obj.hom)) (by
      change X.obj.hom ≫ L.normalizerSubdivisionEvaluation.map
        (L.normalizerSingletonSelection X.obj.right.chain P (asIso X.obj.hom)) = 𝟙 P
      rw [L.normalizerSingletonSelection_evaluation]
      exact IsIso.hom_inv_id X.obj.hom))

theorem normalizerEvaluationPointArrow_unique (P : L.Object) (X : L.NormalizerEvaluationPointed P)
    (f : X ⟶ L.normalizerEvaluationPoint P) : f = L.normalizerEvaluationPointArrow P X := by
  letI : IsIso X.obj.hom := X.property
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext
  exact L.normalizerSingletonSelection_unique X.obj.right.chain P (asIso X.obj.hom)
    f.hom.right (StructuredArrow.w f.hom)

def normalizerEvaluationPoint_isTerminal (P : L.Object) :
    Limits.IsTerminal (L.normalizerEvaluationPoint P) :=
  Limits.IsTerminal.ofUniqueHom (L.normalizerEvaluationPointArrow P)
    (L.normalizerEvaluationPointArrow_unique P)

end CentricLinkingSystem
end Sharpness.FusionSystem
