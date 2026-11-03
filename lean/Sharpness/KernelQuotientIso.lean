import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-! A quotient isomorphism with a formula on every representative,
proved with opaque ambient modules before applying it to totalization. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
variable {R V W : Type u} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) (P : Submodule R V) (hk : f.ker = P) (hf : Function.Surjective f)

def quotientIsoOfKer : ModuleCat.of R (V ⧸ P) ≅ ModuleCat.of R W :=
  ((Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hf)).toModuleIso

theorem quotientIsoOfKer_mk (x : V) :
    (quotientIsoOfKer f P hk hf).hom (Submodule.Quotient.mk x) = f x := by
  change f.quotKerEquivOfSurjective hf
    (Submodule.quotEquivOfEq P f.ker hk.symm (Submodule.Quotient.mk x)) = f x
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

end Sharpness
