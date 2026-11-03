import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
Exact colimits commute with homology.  The comparison used below is the
canonical map of the actual colimit cocone, rather than a chosen objectwise
isomorphism.  These lemmas are independent of fusion systems and of any
vanishing theorem.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v w

namespace Sharpness.V29
open CategoryTheory CategoryTheory.Limits

section ShortComplex
variable {C : Type v} {J : Type u} [Category.{u} C] [Abelian C] [Category.{u} J]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

/-- Homology in a functor category is evaluated pointwise, with its actual
maps.  This natural isomorphism is used before taking the colimit. -/
def shortComplexPointwiseHomologyIso (F : J ⥤ ShortComplex C) :
    F ⋙ ShortComplex.homologyFunctor C ≅
      ((ShortComplex.functorEquivalence J C).inverse.obj F).homology := by
  let S := (ShortComplex.functorEquivalence J C).inverse.obj F
  refine NatIso.ofComponents (fun j => S.mapHomologyIso ((evaluation J C).obj j)) ?_
  intro i j f
  change ShortComplex.homologyMap (S.mapNatTrans ((evaluation J C).map f)) ≫
      (S.mapHomologyIso ((evaluation J C).obj j)).hom =
    (S.mapHomologyIso ((evaluation J C).obj i)).hom ≫ S.homology.map f
  rw [S.homologyMap_mapNatTrans]
  simp

/-- Applying an exact colimit functor to a short complex computes its homology. -/
def shortComplexColimitHomologyIso (F : J ⥤ ShortComplex C) :
    colimit (F ⋙ ShortComplex.homologyFunctor C) ≅
      (ShortComplex.colimitCocone F).pt.homology :=
  HasColimit.isoOfNatIso (shortComplexPointwiseHomologyIso F) ≪≫
    (((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso
      (colim : (J ⥤ C) ⥤ C)).symm

@[reassoc]
theorem shortComplexColimitHomologyIso_ι (F : J ⥤ ShortComplex C) (j : J) :
    colimit.ι (F ⋙ ShortComplex.homologyFunctor C) j ≫
        (shortComplexColimitHomologyIso F).hom =
      ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app j) := by
  let S := (ShortComplex.functorEquivalence J C).inverse.obj F
  change colimit.ι _ j ≫
      (HasColimit.isoOfNatIso (shortComplexPointwiseHomologyIso F)).hom ≫
        (S.mapHomologyIso (colim : (J ⥤ C) ⥤ C)).inv = _
  rw [HasColimit.isoOfNatIso_ι_hom_assoc]
  exact (S.homologyMap_mapNatTrans (colim.ι j)).symm

/-- The homology functor preserves colimits of every exact shape. -/
instance shortComplexHomologyPreservesColimits :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor C) where
  preservesColimit {F} := by
    apply preservesColimit_of_preserves_colimit_cocone
      (ShortComplex.isColimitColimitCocone F)
    apply IsColimit.ofIsoColimit (colimit.isColimit _)
    exact Cocone.ext (shortComplexColimitHomologyIso F)
      (fun j => shortComplexColimitHomologyIso_ι F j)

end ShortComplex

section Complex
variable {C : Type v} {J : Type u} {I : Type w} [Category.{u} C] [Abelian C] [Category.{u} J]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
  (c : ComplexShape I) (n : I)

instance shortComplexFunctorPreservesColimits :
    PreservesColimitsOfShape J (HomologicalComplex.shortComplexFunctor C c n) where
  preservesColimit {F} := ⟨fun {s} hs => ⟨by
    apply ShortComplex.isColimitOfIsColimitπ
    · exact isColimitOfPreserves (HomologicalComplex.eval C c (c.prev n)) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval C c n) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval C c (c.next n)) hs⟩⟩

/-- Homology in every degree preserves exact colimits of complexes. -/
instance homologyPreservesExactColimits :
    PreservesColimitsOfShape J (HomologicalComplex.homologyFunctor C c n) :=
  preservesColimitsOfShape_of_natIso (HomologicalComplex.homologyFunctorIso C c n).symm

end Complex

section Limits
variable {C : Type v} {J K : Type u} [Category.{u} C] [Category.{u} J] [Category.{u} K]
  [HasColimitsOfShape J C] [HasLimitsOfShape K C]
  [PreservesLimitsOfShape K (colim : (J ⥤ C) ⥤ C)]

/-- The two equivalent orders of an exact colimit and a finite limit, in the
orientation needed for a colimit-preservation statement. -/
def limitColimitInterchange (F : J ⥤ K ⥤ C) :
    colimit (F ⋙ lim) ≅ limit (colimit F) :=
  HasColimit.isoOfNatIso (limitFlipIsoCompLim F).symm ≪≫ colimitLimitIso F.flip

@[reassoc]
theorem limitColimitInterchange_ι_π (F : J ⥤ K ⥤ C) (j : J) (k : K) :
    colimit.ι (F ⋙ lim) j ≫ (limitColimitInterchange F).hom ≫
      limit.π (colimit F) k =
    limit.π (F.obj j) k ≫ (colimit.ι F j).app k := by
  dsimp only [limitColimitInterchange, Iso.trans_hom]
  simp only [Category.assoc]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc]
  erw [ι_colimitLimitIso_limit_π]
  simp [limitFlipIsoCompLim]
  rfl

/-- If `J`-colimits preserve `K`-limits, the `K`-limit functor preserves
`J`-colimits. -/
instance limitPreservesExactColimits :
    PreservesColimitsOfShape J (lim : (K ⥤ C) ⥤ C) where
  preservesColimit {F} := by
    have he : colimit.post F lim = (limitColimitInterchange F).hom := by
      apply colimit.hom_ext
      intro j
      apply limit.hom_ext
      intro k
      simp only [Category.assoc, colimit.ι_post_assoc,
        limitColimitInterchange_ι_π]
      exact limit.lift_π _ _
    have : IsIso (colimit.post F lim) := by rw [he]; infer_instance
    exact preservesColimit_of_isIso_post lim F

end Limits
end Sharpness.V29
