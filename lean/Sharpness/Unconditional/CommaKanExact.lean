import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! Exact right Kan extension when each pointwise comma category admits
an initial discrete family. The formula is a product of evaluations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

variable (R : Type u) [CommRing R]
    {A B : Type u} [Category.{u} A] [Category.{u} B] (L : A ⥤ B)

instance moduleRanIsRightAdjoint : (L.ran (H := ModuleCat.{u} R)).IsRightAdjoint :=
  (L.ranAdjunction (ModuleCat.{u} R)).isRightAdjoint

/-- The usual pointwise right-Kan formula, natural in the coefficient diagram. -/
def ranEvaluationCommaLimitIso (b : B) :
    L.ran ⋙ (evaluation B (ModuleCat.{u} R)).obj b ≅
      (whiskeringLeft (StructuredArrow b L) A (ModuleCat.{u} R)).obj
        (StructuredArrow.proj b L) ⋙ lim :=
  NatIso.ofComponents (fun D => L.ranObjObjIsoLimit D b) (by
    intro D E α
    change (L.ran.map α).app b ≫ (L.ranObjObjIsoLimit E b).hom =
      (L.ranObjObjIsoLimit D b).hom ≫ limMap (Functor.whiskerLeft (StructuredArrow.proj b L) α)
    apply limit.hom_ext
    intro X
    simp only [Category.assoc, ranObjObjIsoLimit_hom_π, limMap_π]
    rw [← Category.assoc, ← (L.ran.map α).naturality]
    simp only [Category.assoc]
    rw [← Category.assoc (L.ranObjObjIsoLimit D b).hom, ranObjObjIsoLimit_hom_π]
    have h := congr_app (L.ranCounit.naturality α) X.right
    dsimp at h
    simpa only [Category.assoc, Functor.whiskerLeft_app, StructuredArrow.proj_obj] using congrArg
      (fun f => (L.ran.obj D).map X.hom ≫ f) h)

/-- Initial representatives of comma components calculate Ran by a product. -/
def ranObjIsoProduct (b : B) {I : Type u}
    (ι : Discrete I ⥤ StructuredArrow b L) [ι.Initial] (D : A ⥤ ModuleCat.{u} R) :
    (L.ran.obj D).obj b ≅ ∏ᶜ (fun i : I => D.obj (ι.obj ⟨i⟩).right) :=
  L.ranObjObjIsoLimit D b ≪≫
    (Functor.Initial.limitIso ι (StructuredArrow.proj b L ⋙ D)).symm ≪≫
    HasLimit.isoOfNatIso (Discrete.natIso (fun _ => Iso.refl _))

@[reassoc]
theorem ranObjIsoProduct_hom_π (b : B) {I : Type u}
    (ι : Discrete I ⥤ StructuredArrow b L) [ι.Initial] (D : A ⥤ ModuleCat.{u} R)
    (i : I) :
    (ranObjIsoProduct R L b ι D).hom ≫ Pi.π _ i =
      (L.ran.obj D).map (ι.obj ⟨i⟩).hom ≫ (L.ranCounit.app D).app (ι.obj ⟨i⟩).right := by
  simp [ranObjIsoProduct, Pi.π, HasLimit.isoOfNatIso_hom_π,
    Functor.Initial.limitIso_inv, limit.pre_π, ranObjObjIsoLimit_hom_π]

/-- An initial discrete family makes limits of modules exact. -/
theorem exactLimits_of_initialDiscrete {J : Type u} [Category.{u} J] {I : Type u}
    (ι : Discrete I ⥤ J) [ι.Initial] : HasExactLimitsOfShape J (ModuleCat.{u} R) :=
  hasExactLimitsOfShape_of_initial (ModuleCat.{u} R) ι

/-- Pointwise comma decompositions into components with initial representatives
imply that right Kan extension preserves epimorphisms. -/
theorem ran_preservesEpimorphisms_of_initialDiscrete
    (I : B → Type u) (ι : ∀ b, Discrete (I b) ⥤ StructuredArrow b L)
    (hι : ∀ b, (ι b).Initial) :
    (L.ran (H := ModuleCat.{u} R)).PreservesEpimorphisms where
  preserves {D E} α := by
    intro
    haveI : ∀ b, Epi ((L.ran.map α).app b) := by
      intro b
      letI := hι b
      letI := exactLimits_of_initialDiscrete R (ι b)
      let G := (whiskeringLeft (StructuredArrow b L) A (ModuleCat.{u} R)).obj
        (StructuredArrow.proj b L) ⋙ lim
      haveI : G.PreservesEpimorphisms := by
        dsimp [G]
        infer_instance
      let H := L.ran ⋙ (evaluation B (ModuleCat.{u} R)).obj b
      haveI : H.PreservesEpimorphisms :=
        Functor.preservesEpimorphisms.of_iso (ranEvaluationCommaLimitIso R L b).symm
      exact Functor.map_epi H α
    exact NatTrans.epi_of_epi_app _

/-- Together with the right-adjoint kernel preservation, the same formula
gives exactness in the form used by the derived-functor comparison. -/
theorem ran_preservesHomology_of_initialDiscrete
    (I : B → Type u) (ι : ∀ b, Discrete (I b) ⥤ StructuredArrow b L)
    (hι : ∀ b, (ι b).Initial) :
    (L.ran (H := ModuleCat.{u} R)).PreservesHomology := by
  letI := ran_preservesEpimorphisms_of_initialDiscrete R L I ι hι
  letI : (L.ran (H := ModuleCat.{u} R)).IsRightAdjoint :=
    (L.ranAdjunction (ModuleCat.{u} R)).isRightAdjoint
  haveI : (L.ran (H := ModuleCat.{u} R)).PreservesZeroMorphisms := by infer_instance
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

end Sharpness
