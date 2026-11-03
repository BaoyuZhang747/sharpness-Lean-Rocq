import Sharpness.Unconditional.RightKanAcyclicComparisonResolution
import Sharpness.Unconditional.FiberDetection

/-! Actual higher-limit comparison for a prefibered functor whose coefficient
diagram has vanishing positive higher limits on each strict fibre. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (R : Type u) [CommRing R]
    {A B : Type u} [Category.{u} A] [Category.{u} B]
    (r : A ⥤ B) [r.IsPreFibered]

theorem ran_injectiveResolution_positiveExact_of_fibers
    (D : A ⥤ ModuleCat.{u} R) (I : InjectiveResolution D)
    (h : ∀ (b : B) (n : ℕ),
      IsZero (covariantHigherLimit R (Fiber.fiberInclusion (p := r) (S := b) ⋙ D) (n + 1)))
    (n : ℕ) : ((r.ran.mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1) := by
  apply functorCochain_exactAt_of_evaluations R
  intro b
  let E := (whiskeringLeft (Fiber r b) A (ModuleCat.{u} R)).obj Fiber.fiberInclusion
  let J := mapInjectiveResolution E I
  have hh := (ext_isZero_iff_injectiveHom_exactAt R
    ((Functor.const (Fiber r b)).obj (ModuleCat.of R R)) (E.obj D) J (n + 1)).mp (h b n)
  let e₁ := (NatIso.mapHomologicalComplex (constantHomLimitIso R (Fiber r b))
    (ComplexShape.up ℕ)).app J.cocomplex
  let e₂ := (NatIso.mapHomologicalComplex (ranEvaluationFiberLimitIso R r b)
    (ComplexShape.up ℕ)).app I.cocomplex
  exact (hh.of_iso e₁).of_iso e₂.symm

/-- All-degree module isomorphism; in particular degree zero is retained. -/
def covariantHigherLimitRanIsoOfFiberAcyclicity
    (D : A ⥤ ModuleCat.{u} R)
    (h : ∀ (b : B) (n : ℕ),
      IsZero (covariantHigherLimit R (Fiber.fiberInclusion (p := r) (S := b) ⋙ D) (n + 1)))
    (n : ℕ) : covariantHigherLimit R D n ≅ covariantHigherLimit R (r.ran.obj D) n :=
  extRightAdjointIsoOfPositiveExactness R (r.ranAdjunction (ModuleCat.{u} R))
    ((Functor.const B).obj (ModuleCat.of R R)) D (injectiveResolution D)
    (ran_injectiveResolution_positiveExact_of_fibers R r D (injectiveResolution D) h) n

end Sharpness
