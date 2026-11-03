import Sharpness.LibmanNormalizerInput
import Sharpness.NormalizerCochainDiagram
import Sharpness.ReplacementConeAugmentation

/-! Actual forgetful maps of the fixed comma model give a strict
cocone to the linking space. Its singular pullbacks define the actual
cochain augmentation and the actual restriction to the native inverse
limit. Every chain component retains the first-coordinate classifying
map. No equivalence or edge-isomorphism assertion is assumed here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat)

def nerveCocone : I.toLibmanNormalizerData.categoryDiagram ⋙ CategoryTheory.nerveFunctor ⟶
    (Functor.const F.NormalizerCategory).obj (CategoryTheory.nerve L.Object) where
  app d := CategoryTheory.nerveMap (CostructuredArrow.proj I.projection d ⋙ I.evaluation)
  naturality {d e} a := by
    change CategoryTheory.nerveMap (CostructuredArrow.map a) ≫
        CategoryTheory.nerveMap (CostructuredArrow.proj I.projection e ⋙ I.evaluation) =
      CategoryTheory.nerveMap (CostructuredArrow.proj I.projection d ⋙ I.evaluation) ≫ 𝟙 _
    rw [Category.comp_id]
    rfl

def forgetMap (d : F.NormalizerCategory) :
    I.toLibmanNormalizerData.diagram.obj d ⟶ L.classifyingSpace :=
  SSet.toTop.map (I.nerveCocone.app d)

theorem forgetMap_naturality {d e : F.NormalizerCategory} (a : d ⟶ e) :
    I.toLibmanNormalizerData.diagram.map a ≫ I.forgetMap e = I.forgetMap d := by
  have h := (I.nerveCocone.naturality a).trans (Category.comp_id _)
  exact (SSet.toTop.map_comp _ _).symm.trans (congrArg (fun f => SSet.toTop.map f) h)

theorem chainComparisonMap_forget (σ : F.CentricChain) :
    I.toLibmanNormalizerData.chainComparisonMap σ ≫ I.forgetMap (F.normalizerClass σ) =
      L.chainClassifyingMap σ := by
  have h := congrArg (fun T => nerveMapSingleObj (L.ChainAut σ) T)
    (I.comparison_factorization σ)
  rw [nerveMapSingleObj_comp] at h
  exact (SSet.toTop.map_comp _ _).symm.trans (congrArg (fun f => SSet.toTop.map f) h)

variable (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

def cochainRestrictionCone :
    (Functor.const F.NormalizerCategoryᵒᵖ).obj (SingularCohomology.cochains R L.classifyingSpace A) ⟶
      I.toLibmanNormalizerData.cochainDiagram R A where
  app d := SingularCohomology.cochainPull R (I.forgetMap d.unop) A
  naturality {d e} a := by
    change (𝟙 _) ≫ SingularCohomology.cochainPull R (I.forgetMap e.unop) A =
      SingularCohomology.cochainPull R (I.forgetMap d.unop) A ≫
        SingularCohomology.cochainPull R (I.toLibmanNormalizerData.diagram.map a.unop) A
    rw [Category.id_comp, ← SingularCohomology.cochainPull_comp, I.forgetMap_naturality]

def cochainAugmentation :
    SingularCohomology.cochains R L.classifyingSpace A ⟶ I.toLibmanNormalizerData.totalCochains R A :=
  replacementConeAugmentation (I.toLibmanNormalizerData.cochainDiagram R A) (I.cochainRestrictionCone R A)

theorem cochainAugmentation_projection (d : F.NormalizerCategory) (n : ℕ) :
    (I.cochainAugmentation R A).f n ≫
      totalSummandProjectionAt (I.toLibmanNormalizerData.bicomplex R A) 0 n n (by omega) ≫
        (productCochainsProjection
          (fun t : ComposableArrows F.NormalizerCategory 0 =>
            (I.toLibmanNormalizerData.cochainDiagram R A).obj (op (chainHead t)))
          (ComposableArrows.mk₀ d)).f n =
      (SingularCohomology.cochainPull R (I.forgetMap d) A).f n :=
  replacementConeAugmentation_projection (I.toLibmanNormalizerData.cochainDiagram R A)
    (I.cochainRestrictionCone R A) n (ComposableArrows.mk₀ d)

def restrictionCone (n : ℕ) : Cone (I.toLibmanNormalizerData.cohomologyDiagram R A n) where
  pt := SingularCohomology.cohomology R L.classifyingSpace A n
  π :=
    { app d := SingularCohomology.pull R (I.forgetMap d.unop) A n
      naturality {d e} a := by
        change (𝟙 _) ≫ SingularCohomology.pull R (I.forgetMap e.unop) A n =
          SingularCohomology.pull R (I.forgetMap d.unop) A n ≫
            SingularCohomology.pull R (I.toLibmanNormalizerData.diagram.map a.unop) A n
        rw [Category.id_comp, ← SingularCohomology.pull_comp, I.forgetMap_naturality] }

def restrictionToLimit (n : ℕ) :
    SingularCohomology.cohomology R L.classifyingSpace A n ⟶
      limit (I.toLibmanNormalizerData.cohomologyDiagram R A n) :=
  limit.lift _ (I.restrictionCone R A n)

theorem restrictionToLimit_component (n : ℕ) (d : F.NormalizerCategory) :
    I.restrictionToLimit R A n ≫ limit.π _ (op d) =
      SingularCohomology.pull R (I.forgetMap d) A n := limit.lift_π _ _

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
