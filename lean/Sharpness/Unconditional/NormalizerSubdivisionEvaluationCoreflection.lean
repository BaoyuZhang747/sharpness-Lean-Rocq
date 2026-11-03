import Sharpness.Unconditional.NormalizerSubdivisionEvaluationPrefix
import Mathlib.CategoryTheory.Adjunction.Basic

/-! The full subcategory of the evaluation undercategory in which the
structural arrow is invertible is coreflective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

abbrev NormalizerEvaluationUnder (P : L.Object) :=
  StructuredArrow P L.normalizerSubdivisionEvaluation

def normalizerEvaluationPointedProperty (P : L.Object) :
    ObjectProperty (L.NormalizerEvaluationUnder P) := fun X => IsIso X.hom

abbrev NormalizerEvaluationPointed (P : L.Object) :=
  (L.normalizerEvaluationPointedProperty P).FullSubcategory

def normalizerEvaluationPointedInclusion (P : L.Object) :
    L.NormalizerEvaluationPointed P ⥤ L.NormalizerEvaluationUnder P :=
  (L.normalizerEvaluationPointedProperty P).ι

/-- Concrete universal-arrow data, constructed below from the linking axioms. -/
structure NormalizerEvaluationCoreflectionData (P : L.Object)
    (X : L.NormalizerEvaluationUnder P) where
  point : L.NormalizerEvaluationPointed P
  deletion : point.obj ⟶ X
  universal : ∀ (Y : L.NormalizerEvaluationPointed P) (f : Y.obj ⟶ X),
    ∃! g : Y.obj ⟶ point.obj, g ≫ deletion = f

def normalizerEvaluationCoreflectionData (P : L.Object)
    (X : L.NormalizerEvaluationUnder P) : L.NormalizerEvaluationCoreflectionData P X := by
  classical
  by_cases hc : Nat.card P.as.val = Nat.card (X.right.chain.subgroup 0)
  · let a := L.normalizerLinkingIsoOfEqualCard X.hom hc
    have ha : a.hom = X.hom := L.normalizerLinkingIsoOfEqualCard_hom X.hom hc
    have hi : IsIso X.hom := by rw [← ha]; infer_instance
    refine ⟨⟨X, hi⟩, 𝟙 X, ?_⟩
    intro Y f
    exact ⟨f, Category.comp_id f, fun g hg => (Category.comp_id g).symm.trans hg⟩
  · let I := L.normalizerLinkingImage X.hom
    let a := L.normalizerLinkingImageIso X.hom
    have hI : I.as.val < X.right.chain.subgroup 0 := L.normalizerLinkingImage_lt X.hom hc
    let Z : L.NormalizerEvaluationUnder P := StructuredArrow.mk (Y :=
      L.normalizerSubdivisionObj (X.right.chain.prepend I.as hI)) a.hom
    let d : Z ⟶ X := StructuredArrow.homMk
      (L.normalizerPrependDeletion X.right.chain I hI) (by
        change a.hom ≫ L.normalizerSubdivisionEvaluation.map
          (L.normalizerPrependDeletion X.right.chain I hI) = X.hom
        rw [L.normalizerPrependDeletion_evaluation]
        exact L.normalizerLinkingImage_factorization X.hom)
    refine ⟨⟨Z, a.isIso_hom⟩, d, ?_⟩
    intro Y f
    letI : IsIso Y.obj.hom := Y.property
    let b : Y.obj.right.chain.linkingObject L 0 ≅ I := (asIso Y.obj.hom).symm.trans a
    have hb : b.hom ≫ L.inclusionLift hI.le =
        L.normalizerSubdivisionEvaluation.map f.right := by
      apply (cancel_epi Y.obj.hom).mp
      change Y.obj.hom ≫ ((inv Y.obj.hom ≫ a.hom) ≫ _) = _
      simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
      exact (L.normalizerLinkingImage_factorization X.hom).trans (StructuredArrow.w f).symm
    let k := L.normalizerPrependLift Y.obj.right.chain X.right.chain I hI f.right b hb
    let g : Y.obj ⟶ Z := StructuredArrow.homMk k (by
      change Y.obj.hom ≫ L.normalizerSubdivisionEvaluation.map k = a.hom
      rw [L.normalizerPrependLift_evaluation]
      change Y.obj.hom ≫ (inv Y.obj.hom ≫ a.hom) = a.hom
      rw [IsIso.hom_inv_id_assoc])
    have hg : g ≫ d = f := by
      apply StructuredArrow.hom_ext
      exact L.normalizerPrependLift_deletion Y.obj.right.chain X.right.chain I hI f.right b hb
    refine ⟨g, hg, ?_⟩
    intro g' hg'
    apply StructuredArrow.hom_ext
    apply L.normalizerPrependDeletion_cancel Y.obj.right.chain X.right.chain I hI
    exact congrArg (fun t : Y.obj ⟶ X => t.right) (hg'.trans hg.symm)

def normalizerEvaluationCoreflectionHomEquiv (P : L.Object)
    (Y : L.NormalizerEvaluationPointed P) (X : L.NormalizerEvaluationUnder P) :
    ((L.normalizerEvaluationPointedInclusion P).obj Y ⟶ X) ≃
      (Y ⟶ (L.normalizerEvaluationCoreflectionData P X).point) := by
  let D := L.normalizerEvaluationCoreflectionData P X
  exact (Equiv.ofBijective (fun g : Y ⟶ D.point => g.hom ≫ D.deletion)
    ((Function.bijective_iff_existsUnique _).mpr (fun f => by
      obtain ⟨g, hg, hu⟩ := D.universal Y f
      refine ⟨ObjectProperty.homMk g, hg, ?_⟩
      intro k hk
      apply ObjectProperty.hom_ext
      exact hu k.hom hk))).symm

theorem normalizerEvaluationCoreflectionHomEquiv_naturality (P : L.Object)
    (Y' Y : L.NormalizerEvaluationPointed P) (X : L.NormalizerEvaluationUnder P)
    (f : Y' ⟶ Y) (g : (L.normalizerEvaluationPointedInclusion P).obj Y ⟶ X) :
    L.normalizerEvaluationCoreflectionHomEquiv P Y' X
        ((L.normalizerEvaluationPointedInclusion P).map f ≫ g) =
      f ≫ L.normalizerEvaluationCoreflectionHomEquiv P Y X g := by
  apply (L.normalizerEvaluationCoreflectionHomEquiv P Y' X).symm.injective
  rw [Equiv.symm_apply_apply]
  change f.hom ≫ g =
    (f.hom ≫ (L.normalizerEvaluationCoreflectionHomEquiv P Y X g).hom) ≫
      (L.normalizerEvaluationCoreflectionData P X).deletion
  rw [Category.assoc]
  exact congrArg (fun k => f.hom ≫ k)
    ((L.normalizerEvaluationCoreflectionHomEquiv P Y X).symm_apply_apply g).symm

def normalizerEvaluationCoreflection (P : L.Object) :
    L.NormalizerEvaluationUnder P ⥤ L.NormalizerEvaluationPointed P :=
  Adjunction.rightAdjointOfEquiv (L.normalizerEvaluationCoreflectionHomEquiv P)
    (L.normalizerEvaluationCoreflectionHomEquiv_naturality P)

def normalizerEvaluationCoreflectionAdjunction (P : L.Object) :
    L.normalizerEvaluationPointedInclusion P ⊣ L.normalizerEvaluationCoreflection P :=
  Adjunction.adjunctionOfEquivRight (L.normalizerEvaluationCoreflectionHomEquiv P)
    (L.normalizerEvaluationCoreflectionHomEquiv_naturality P)

end Sharpness.FusionSystem.CentricLinkingSystem
