import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module

/-! Explicit module direct sums and their universal morphisms. The
index need not be finite, and all formulas are stated on actual
summand inclusions. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness
open CategoryTheory
open scoped DirectSum
variable {R : Type u} [CommRing R] {ι : Type v} (M : ι → ModuleCat.{max u v} R)

local instance moduleDirectSumIndexDecidableEq : DecidableEq ι := Classical.decEq _

def moduleDirectSum : ModuleCat.{max u v} R := ModuleCat.of R (⨁ i, M i)

def moduleDirectSumInclusion (i : ι) : M i ⟶ moduleDirectSum M :=
  ModuleCat.ofHom (DirectSum.lof R ι (fun i => M i) i)

def moduleDirectSumDesc {A : ModuleCat.{max u v} R} (f : ∀ i, M i ⟶ A) : moduleDirectSum M ⟶ A :=
  ModuleCat.ofHom (DirectSum.toModule R ι A (fun i => (f i).hom))

@[reassoc]
theorem moduleDirectSumInclusion_desc {A : ModuleCat.{max u v} R} (f : ∀ i, M i ⟶ A) (i : ι) :
    moduleDirectSumInclusion M i ≫ moduleDirectSumDesc M f = f i := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change DirectSum.toModule R ι A (fun j => (f j).hom)
    (DirectSum.lof R ι (fun j => M j) i x) = (f i).hom x
  exact DirectSum.toModule_lof R (M := fun j => M j) (N := A)
    (φ := fun j => (f j).hom) i x

theorem moduleDirectSum_hom_ext {A : ModuleCat.{max u v} R} {f g : moduleDirectSum M ⟶ A}
    (h : ∀ i, moduleDirectSumInclusion M i ≫ f = moduleDirectSumInclusion M i ≫ g) : f=g := by
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro i
  exact congrArg ModuleCat.Hom.hom (h i)

end Sharpness
