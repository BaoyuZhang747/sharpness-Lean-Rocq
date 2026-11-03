import Sharpness.BarScalarDivisibility
import Sharpness.LocalCoefficients

/-! Finite generation of actual finite bar cohomology and the Nakayama
deduction. This proves the finite-generation step instead of adding a
higher-limit finiteness assertion to the reference interface. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FiniteBarModel
open CategoryTheory
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (B : FiniteBarModel R C) (D : CoefficientCategory R C)

instance cochains_finite [∀ P, Module.Finite R (D.obj P)] (n : ℕ) :
    Module.Finite R (B.Cochains D n) :=
  inferInstanceAs (Module.Finite R (∀ i : B.Index n, D.obj (B.source n i)))

instance cohomology_finite [IsNoetherianRing R]
    [∀ P, Module.Finite R (D.obj P)] (n : ℕ) : Module.Finite R (B.Cohomology D n) := by
  haveI : Module.Finite R (B.Cochains D (n+1)) := B.cochains_finite D (n+1)
  exact inferInstanceAs (Module.Finite R
    (B.cycles D n ⧸ LinearMap.range (B.boundary D n)))

theorem exactPositive_of_fg_of_scalar_surjective [IsNoetherianRing R]
    [∀ P, Module.Finite R (D.obj P)]
    (r : R) (hr : r ∈ Ideal.jacobson (⊥ : Ideal R))
    (surj : ∀ n, Function.Surjective (fun x : B.Cohomology D n => r • x)) :
    B.ExactPositive D := by
  apply (B.exactPositive_iff D).mpr
  intro n
  exact subsingleton_of_forall_eq 0
    (Sharpness.zero_of_fg_of_scalar_surjective r hr (surj n))

end Sharpness.FiniteBarModel
