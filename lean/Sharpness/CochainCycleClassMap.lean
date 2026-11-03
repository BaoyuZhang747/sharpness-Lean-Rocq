import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! The actual cohomology map takes a cycle class to the class of its
image. The representative and its closedness proof are explicit. -/
set_option autoImplicit false
noncomputable section
universe u v t
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type t} {c : ComplexShape ι} {K L : HomologicalComplex C c} (φ : K ⟶ L)

theorem cochainCycle_map_closed {M : C} (i j : ι) (x : M ⟶ K.X i)
    (hx : x ≫ K.d i j = 0) : (x ≫ φ.f i) ≫ L.d i j = 0 := by
  rw [Category.assoc, φ.comm, ← Category.assoc, hx, zero_comp]

theorem cochainCycleClass_map {M : C} (i j : ι) (hj : c.next i = j)
    (x : M ⟶ K.X i) (hx : x ≫ K.d i j = 0) :
    (K.liftCycles x j hj hx ≫ K.homologyπ i) ≫ HomologicalComplex.homologyMap φ i =
    L.liftCycles (x ≫ φ.f i) j hj (by
      rw [Category.assoc, φ.comm, ← Category.assoc, hx, zero_comp]) ≫ L.homologyπ i := by
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]

end Sharpness
