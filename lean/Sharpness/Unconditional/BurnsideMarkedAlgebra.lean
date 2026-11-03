import Sharpness.Unconditional.BurnsideMarks
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! A faithful multiplicative table of marks constructs an actual algebra
as its range. Its units act invertibly in every compatible linear action. -/
set_option autoImplicit false
noncomputable section
universe u v w

namespace Sharpness.Burnside

variable (R : Type u) [CommRing R] (ι : Type w)

/-- Explicit linear mark data, with the product and unit identities that
hold for the concrete slice decomposition. Ring laws will be inherited
from the actual subalgebra of functions, rather than assumed separately. -/
structure MarkedAlgebraData where
  mark : (ι →₀ R) →ₗ[R] (ι → R)
  mark_injective : Function.Injective mark
  unit : ι →₀ R
  mul : (ι →₀ R) →ₗ[R] (ι →₀ R) →ₗ[R] (ι →₀ R)
  mark_unit : mark unit = 1
  mark_mul : ∀ a b, mark (mul a b) = mark a * mark b

namespace MarkedAlgebraData

variable {R ι} (D : MarkedAlgebraData R ι)

/-- The range of the mark map is an actual commutative R-algebra. -/
def toSubalgebra : Subalgebra R (ι → R) where
  carrier := Set.range D.mark
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, D.mark.map_add a b⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨D.mul a b, D.mark_mul a b⟩
  algebraMap_mem' r := by
    refine ⟨r • D.unit, ?_⟩
    rw [map_smul, D.mark_unit]
    ext i
    simp

/-- Marks restricted to their actual range. -/
def toLinearMap : (ι →₀ R) →ₗ[R] D.toSubalgebra where
  toFun a := ⟨D.mark a, ⟨a, rfl⟩⟩
  map_add' a b := Subtype.ext (D.mark.map_add a b)
  map_smul' r a := Subtype.ext (D.mark.map_smul r a)

/-- The additive module of the range algebra is the original free module. -/
def equiv : (ι →₀ R) ≃ₗ[R] D.toSubalgebra :=
  LinearEquiv.ofBijective D.toLinearMap
    ⟨fun _ _ h => D.mark_injective (congrArg Subtype.val h),
      fun a => by
        obtain ⟨b, hb⟩ := a.property
        exact ⟨b, Subtype.ext hb⟩⟩

@[simp] theorem equiv_apply_val (a : ι →₀ R) : (D.equiv a).val = D.mark a := rfl

@[simp] theorem equiv_unit : D.equiv D.unit = 1 := Subtype.ext D.mark_unit

@[simp] theorem equiv_mul (a b : ι →₀ R) : D.equiv (D.mul a b) = D.equiv a * D.equiv b :=
  Subtype.ext (D.mark_mul a b)

@[simp] theorem equiv_symm_one : D.equiv.symm 1 = D.unit :=
  D.equiv.symm_apply_eq.mpr D.equiv_unit.symm

@[simp] theorem equiv_symm_mul (a b : D.toSubalgebra) :
    D.equiv.symm (a * b) = D.mul (D.equiv.symm a) (D.equiv.symm b) := by
  apply D.equiv.injective
  simp

/-- The original formal generators remain a basis of the range algebra. -/
def basis : Module.Basis ι R D.toSubalgebra := Finsupp.basisSingleOne.map D.equiv

/-- Coordinate evaluations are algebra characters. -/
def character (i : ι) : D.toSubalgebra →ₐ[R] R :=
  (Pi.evalAlgHom R (fun _ : ι => R) i).comp D.toSubalgebra.val

@[simp] theorem character_equiv (i : ι) (a : ι →₀ R) :
    D.character i (D.equiv a) = D.mark a i := rfl

/-- The raw table, so concrete users need not unfold the range algebra. -/
def table : Matrix ι ι R := fun i j => D.mark (Finsupp.single j 1) i

theorem markMatrix_eq_table : markMatrix D.basis D.character = D.table := by
  ext i j
  simp [markMatrix, basis, table, Finsupp.coe_basisSingleOne]

variable {T : Type v} [Ring T] [Algebra R T]
    (action : (ι →₀ R) →ₗ[R] T)
    (action_unit : action D.unit = 1)
    (action_mul : ∀ a b, action (D.mul a b) = action a * action b)

/-- Every compatible linear action is an algebra homomorphism from the
constructed range algebra. The target need not be commutative. -/
def actionHom : D.toSubalgebra →ₐ[R] T :=
  AlgHom.ofLinearMap (action.comp D.equiv.symm.toLinearMap)
    (by simpa using action_unit)
    (by intro a b; simpa using action_mul (D.equiv.symm a) (D.equiv.symm b))

@[simp] theorem actionHom_equiv (a : ι →₀ R) :
    D.actionHom action action_unit action_mul (D.equiv a) = action a := by
  change action (D.equiv.symm (D.equiv a)) = action a
  rw [D.equiv.symm_apply_apply]

include action_unit action_mul

/-- A nondegenerate table and unit-valued marks make the actual operator
invertible, even when the table determinant is not a unit. -/
theorem isUnit_action_of_marks [Fintype ι] [DecidableEq ι] [IsDomain R]
    (hdet : D.table.det ≠ 0) (a : ι →₀ R)
    (ha : ∀ i, IsUnit (D.mark a i)) : IsUnit (action a) := by
  have hu : IsUnit (D.equiv a) := isUnit_of_marks D.basis D.character
    (by rwa [D.markMatrix_eq_table]) (D.equiv a) (by simpa using ha)
  simpa using hu.map (D.actionHom action action_unit action_mul)

end MarkedAlgebraData
end Sharpness.Burnside
