import Sharpness.CochainModuleClasses
import Mathlib.LinearAlgebra.Isomorphisms

/-! Recover actual module-valued homology from a linear presentation by
cocycles whose kernel is precisely the boundaries. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R]

def cochainHomologyIsoOfPresentation
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (V : ModuleCat.{u} R) (f : cochainKernel K n →ₗ[R] V)
    (hsurj : Function.Surjective f)
    (hker : LinearMap.ker f = cochainBoundaries K n) :
    K.homology n ≅ V :=
  cochainClassIso K n ≪≫
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (f.quotKerEquivOfSurjective hsurj)).toModuleIso

end Sharpness
