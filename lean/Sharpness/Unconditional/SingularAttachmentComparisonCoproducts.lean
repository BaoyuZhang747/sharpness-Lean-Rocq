import Sharpness.Unconditional.SingularChainExcisionRelative
import Mathlib.Topology.ContinuousMap.Sigma
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! Singular simplices and actual singular chains preserve arbitrary coproducts.
The geometric input is the connectedness of the nonempty standard simplex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.SingularAttachmentComparison
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open Sharpness.SingularChainExcision

variable {ι : Type u} (X : ι → TopCat.{u})

def singularSigmaSimplexEquiv (n : SimplexCategoryᵒᵖ) :
    (Σ i, (TopCat.toSSet.obj (X i)).obj n) ≃
      (TopCat.toSSet.obj (TopCat.of (Σ i, X i))).obj n :=
  (Equiv.sigmaCongrRight fun i => (X i).toSSetObjEquiv n).trans
    ((ContinuousMap.sigmaCodHomeomorph
      (_root_.stdSimplex ℝ (Fin (n.unop.len + 1))) (fun i => X i)).symm.toEquiv.trans
      ((TopCat.of (Σ i, X i)).toSSetObjEquiv n).symm)

theorem singularSigmaSimplexEquiv_apply (n : SimplexCategoryᵒᵖ)
    (i : ι) (σ : (TopCat.toSSet.obj (X i)).obj n) :
    singularSigmaSimplexEquiv X n ⟨i, σ⟩ =
      (TopCat.toSSet.map (TopCat.sigmaι X i)).app n σ := rfl

def singularSigmaCofan : Cofan (fun i => TopCat.toSSet.obj (X i)) :=
  Cofan.mk (TopCat.toSSet.obj (TopCat.of (Σ i, X i)))
    (fun i => TopCat.toSSet.map (TopCat.sigmaι X i))

def singularSigmaCofanIsColimit : IsColimit (singularSigmaCofan X) := by
  apply evaluationJointlyReflectsColimits
  intro n
  refine (Cofan.isColimitMapCoconeEquiv
    ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n) _ (singularSigmaCofan X)).symm ?_
  apply Classical.choice
  rw [Cofan.nonempty_isColimit_iff_bijective_fromSigma]
  exact (singularSigmaSimplexEquiv X n).bijective

instance singular_preservesCoproduct : PreservesColimit (Discrete.functor X) TopCat.toSSet := by
  apply preservesColimit_of_preserves_colimit_cocone (TopCat.sigmaCofanIsColimit X)
  exact (Cofan.isColimitMapCoconeEquiv _ _ _).symm (singularSigmaCofanIsColimit X)

instance singular_preservesCoproductsOfShape :
    PreservesColimitsOfShape (Discrete ι) TopCat.toSSet.{u} := by
  constructor
  intro F
  letI := singular_preservesCoproduct (fun i : ι => F.obj ⟨i⟩)
  exact preservesColimit_of_iso_diagram TopCat.toSSet (Discrete.natIsoFunctor (F := F)).symm

variable (R : Type u) [CommRing R]

instance singularChains_preservesCoproductsOfShape :
    PreservesColimitsOfShape (Discrete ι) (SingularCohomology.chainsFunctor R) := by
  change PreservesColimitsOfShape (Discrete ι) (TopCat.toSSet ⋙ chains R)
  infer_instance

/-- The actual canonical map from the coproduct of singular chains is an isomorphism. -/
def singularChainsCoproductIso :
    (∐ fun i => (SingularCohomology.chainsFunctor R).obj (X i)) ≅
      (SingularCohomology.chainsFunctor R).obj (∐ X) :=
  (PreservesCoproduct.iso (SingularCohomology.chainsFunctor R) X).symm

theorem singularChainsCoproductIso_ι (i : ι) :
    Sigma.ι (fun i => (SingularCohomology.chainsFunctor R).obj (X i)) i ≫
      (singularChainsCoproductIso X R).hom =
      (SingularCohomology.chainsFunctor R).map (Sigma.ι X i) :=
  ι_comp_sigmaComparison _ _ _

end Sharpness.SingularAttachmentComparison
