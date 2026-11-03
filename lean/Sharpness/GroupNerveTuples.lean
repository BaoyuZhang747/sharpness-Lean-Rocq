import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.SingleObj

/-! Explicit coordinates for the actual nerve of a group. Adjacent
arrows are inverted because composition in SingleObj is reversed
multiplication. These coordinates use Mathlib's native simplices. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory Simplicial
variable (G : Type u) [Group G] (n : ℕ)

def nerveTuple (x : (CategoryTheory.nerve (SingleObj G)).obj (Opposite.op ⦋n⦌)) :
    Fin n → G :=
  fun i => (x.map' i.val (i.val + 1) (Nat.le_succ i.val)
    (Nat.succ_le_of_lt i.isLt))⁻¹

def tupleNerve (g : Fin n → G) :
    (CategoryTheory.nerve (SingleObj G)).obj (Opposite.op ⦋n⦌) :=
  ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star G) (fun i => (g i)⁻¹)

theorem nerveTuple_tupleNerve (g : Fin n → G) :
    nerveTuple G n (tupleNerve G n g) = g := by
  funext i
  simp only [nerveTuple, tupleNerve, ComposableArrows.mkOfObjOfMapSucc_map_succ,
    inv_inv]

theorem tupleNerve_nerveTuple
    (x : (CategoryTheory.nerve (SingleObj G)).obj (Opposite.op ⦋n⦌)) :
    tupleNerve G n (nerveTuple G n x) = x := by
  apply ComposableArrows.ext (fun _ => Subsingleton.elim _ _)
  intro i hi
  simp only [tupleNerve, ComposableArrows.mkOfObjOfMapSucc_map_succ, nerveTuple, inv_inv]
  have h (a b : SingleObj G) (e : a = b) : (eqToHom e : a ⟶ b) = (1 : G) := by
    cases a
    cases b
    rfl
  simp only [h, SingleObj.comp_as_mul, mul_one, one_mul]

def nerveTupleEquiv :
    (CategoryTheory.nerve (SingleObj G)).obj (Opposite.op ⦋n⦌) ≃ (Fin n → G) where
  toFun := nerveTuple G n
  invFun := tupleNerve G n
  left_inv := tupleNerve_nerveTuple G n
  right_inv := nerveTuple_tupleNerve G n

end Sharpness.OrdinaryCohomology
