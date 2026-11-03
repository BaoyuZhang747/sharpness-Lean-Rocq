import Sharpness.Unconditional.RightKanAcyclicComparisonFiber
import Sharpness.Unconditional.RightKanAcyclicComparisonComma

/-! Higher-limit comparison along any functor, from positive higher-limit
vanishing on its actual structured-arrow diagrams. This is an injective
resolution proof and does not require a prefibration or a spectral sequence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (R : Type u) [CommRing R]
    {A B : Type u} [Category.{u} A] [Category.{u} B] (r : A ⥤ B)

theorem ran_injectiveResolution_positiveExact_of_commas
    (D : A ⥤ ModuleCat.{u} R) (I : InjectiveResolution D)
    (h : ∀ (b : B) (n : ℕ),
      IsZero (covariantHigherLimit R (StructuredArrow.proj b r ⋙ D) (n + 1)))
    (n : ℕ) : ((r.ran.mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1) := by
  apply functorCochain_exactAt_of_evaluations R
  intro b
  let E := (whiskeringLeft (StructuredArrow b r) A (ModuleCat.{u} R)).obj
    (StructuredArrow.proj b r)
  let J := mapInjectiveResolution E I
  have hh := (ext_isZero_iff_injectiveHom_exactAt R
    ((Functor.const (StructuredArrow b r)).obj (ModuleCat.of R R))
      (E.obj D) J (n + 1)).mp (h b n)
  let e₁ := (NatIso.mapHomologicalComplex (constantHomLimitIso R (StructuredArrow b r))
    (ComplexShape.up ℕ)).app J.cocomplex
  let e₂ := (NatIso.mapHomologicalComplex (ranEvaluationCommaLimitIso R r b)
    (ComplexShape.up ℕ)).app I.cocomplex
  exact (hh.of_iso e₁).of_iso e₂.symm

/-- Comparison with the actual right Kan extension. The input concerns only
strictly positive local higher limits; ordinary local limits are unrestricted. -/
def covariantHigherLimitRanIsoOfCommaAcyclicity
    (D : A ⥤ ModuleCat.{u} R)
    (h : ∀ (b : B) (n : ℕ),
      IsZero (covariantHigherLimit R (StructuredArrow.proj b r ⋙ D) (n + 1)))
    (n : ℕ) : covariantHigherLimit R D n ≅ covariantHigherLimit R (r.ran.obj D) n :=
  extRightAdjointIsoOfPositiveExactness R (r.ranAdjunction (ModuleCat.{u} R))
    ((Functor.const B).obj (ModuleCat.of R R)) D (injectiveResolution D)
    (ran_injectiveResolution_positiveExact_of_commas R r D (injectiveResolution D) h) n

end Sharpness
