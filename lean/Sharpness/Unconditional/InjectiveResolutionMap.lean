import Sharpness.Unconditional.DerivedDetection
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! Transport injective resolutions through exact functors preserving
injectives, and test exactness of module diagrams objectwise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v w

namespace Sharpness
open CategoryTheory CategoryTheory.Limits

/-- The injective analogue of mathlib's projective-resolution transport. -/
def mapInjectiveResolution
    {C : Type v} [Category.{u} C] [Abelian C]
    {D : Type w} [Category.{u} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]
    {Y : C} (I : InjectiveResolution Y) : InjectiveResolution (F.obj Y) where
  cocomplex := (F.mapHomologicalComplex _).obj I.cocomplex
  injective n := F.injective_obj (I.cocomplex.X n)
  ι := (HomologicalComplex.singleMapHomologicalComplex _ _ _).inv.app Y ≫
    (F.mapHomologicalComplex _).map I.ι
  quasiIso := inferInstance

/-- Exactness of a complex of module diagrams is detected objectwise. -/
theorem functorCochain_exactAt_of_evaluations
    (R : Type u) [CommRing R] {B : Type u} [Category.{u} B]
    (K : CochainComplex (B ⥤ ModuleCat.{u} R) ℕ) (n : ℕ)
    (h : ∀ b : B,
      ((((evaluation B (ModuleCat.{u} R)).obj b).mapHomologicalComplex _).obj K).ExactAt n) :
    K.ExactAt n := by
  apply (HomologicalComplex.exactAt_iff_isZero_homology K n).mpr
  apply Functor.isZero
  intro b
  exact IsZero.of_iso (h b).isZero_homology
    ((K.sc n).mapHomologyIso ((evaluation B (ModuleCat.{u} R)).obj b)).symm

end Sharpness
