import Sharpness.Unconditional.FiberKan
import Sharpness.Unconditional.FiberLan
import Sharpness.Unconditional.LimitHom
import Sharpness.Unconditional.DerivedDetection
import Sharpness.Unconditional.InjectiveResolutionMap
import Sharpness.Unconditional.InjectiveCoefficients
import Sharpness.Unconditional.ProjectiveCoefficients
import Sharpness.ExtZeroTarget

/-! Vanishing of all fiber higher limits detects vanishing of the global
higher limits. The proof uses actual injective resolutions, exact restriction
to fibers, and the pointwise right-Kan formula. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (R : Type u) [CommRing R]
    {A B : Type u} [Category.{u} A] [Category.{u} B]

variable (r : A ⥤ B) [r.IsPreFibered]

instance modulePrecomp_linear :
    ((whiskeringLeft A B (ModuleCat.{u} R)).obj r).Linear R where
  map_smul := by intros; rfl

instance ran_module_additive :
    (r.ran : (A ⥤ ModuleCat.{u} R) ⥤ (B ⥤ ModuleCat.{u} R)).Additive := by
  letI := (r.ranAdjunction (ModuleCat.{u} R)).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products _

instance ran_module_linear : (r.ran : (A ⥤ ModuleCat.{u} R) ⥤ (B ⥤ ModuleCat.{u} R)).Linear R :=
  rightAdjointLinear R (r.ranAdjunction (ModuleCat.{u} R))

/-- All-degree fiber vanishing forces the right Kan extension of an actual
injective resolution to be exact. -/
theorem ran_injectiveResolution_exactAt_of_fibers
    (D : A ⥤ ModuleCat.{u} R) (I : InjectiveResolution D)
    (h : ∀ (b : B) (n : ℕ),
      IsZero (covariantHigherLimit R (Fiber.fiberInclusion (p := r) (S := b) ⋙ D) n))
    (n : ℕ) : ((r.ran.mapHomologicalComplex _).obj I.cocomplex).ExactAt n := by
  apply functorCochain_exactAt_of_evaluations R
  intro b
  let E := (whiskeringLeft (Fiber r b) A (ModuleCat.{u} R)).obj Fiber.fiberInclusion
  let J := mapInjectiveResolution E I
  have hh := (ext_isZero_iff_injectiveHom_exactAt R
    ((Functor.const (Fiber r b)).obj (ModuleCat.of R R)) (E.obj D) J n).mp (h b n)
  let e₁ := (NatIso.mapHomologicalComplex (constantHomLimitIso R (Fiber r b))
    (ComplexShape.up ℕ)).app J.cocomplex
  let e₂ := (NatIso.mapHomologicalComplex (ranEvaluationFiberLimitIso R r b)
    (ComplexShape.up ℕ)).app I.cocomplex
  exact (hh.of_iso e₁).of_iso e₂.symm

/-- The fiber criterion for covariant higher-limit vanishing, in all degrees. -/
theorem covariantHigherLimits_zero_of_fibers
    (D : A ⥤ ModuleCat.{u} R)
    (h : ∀ (b : B) (n : ℕ),
      IsZero (covariantHigherLimit R (Fiber.fiberInclusion (p := r) (S := b) ⋙ D) n))
    (n : ℕ) : IsZero (covariantHigherLimit R D n) := by
  let I := injectiveResolution D
  exact ext_isZero_of_rightAdjoint_acyclic R (r.ranAdjunction (ModuleCat.{u} R))
    ((Functor.const B).obj (ModuleCat.of R R)) D I
    (ran_injectiveResolution_exactAt_of_fibers R r D I h) n

end Sharpness
