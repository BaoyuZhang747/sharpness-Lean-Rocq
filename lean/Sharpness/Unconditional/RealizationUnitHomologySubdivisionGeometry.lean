import Sharpness.Unconditional.RealizationUnitHomologySmallChains
import Mathlib.GroupTheory.Perm.Sign

/-! The actual affine subsimplices used by singular-chain subdivision, together
with preservation of smallness. No boundary identity or excision theorem is
assumed in this geometric construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v
namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped BigOperators

/-- The actual affine map with specified vertices, in barycentric coordinates. -/
def affineSimplexMap {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1))) :
    C(_root_.stdSimplex ℝ (Fin (n + 1)), _root_.stdSimplex ℝ (Fin (m + 1))) where
  toFun t := ⟨fun i => ∑ j, t j * v j i,
    ⟨fun i => Finset.sum_nonneg (fun j _ =>
        mul_nonneg (_root_.stdSimplex.zero_le t j) (_root_.stdSimplex.zero_le (v j) i)), by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, _root_.stdSimplex.sum_eq_one, mul_one]⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun t : _root_.stdSimplex ℝ (Fin (n + 1)) =>
      fun i => ∑ j, t.1 j * (v j).1 i)
    apply continuous_pi
    intro i
    exact continuous_finsetSum _ (fun j _ =>
      ((continuous_apply j).comp continuous_subtype_val).mul continuous_const)

@[simp] theorem affineSimplexMap_apply {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1)))
    (t : _root_.stdSimplex ℝ (Fin (n + 1))) (i : Fin (m + 1)) :
    affineSimplexMap v t i = ∑ j, t j * v j i := rfl

@[simp] theorem affineSimplexMap_vertex {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1))) (j : Fin (n + 1)) :
    affineSimplexMap v (_root_.stdSimplex.vertex j) = v j := by
  apply Subtype.ext
  funext i
  change (∑ k, (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ) k * v k i) = v j i
  simp [Pi.single_apply]

/-- Pull back an actual singular simplex along an actual affine subsimplex. -/
def singularAffinePull {X : TopCat.{u}} {n m : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋m⦌))
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1))) :
    (TopCat.toSSet.obj X).obj (op ⦋n⦌) :=
  (X.toSSetObjEquiv _).symm ((X.toSSetObjEquiv _ σ).comp (affineSimplexMap v))

@[simp] theorem singularAffinePull_apply {X : TopCat.{u}} {n m : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋m⦌))
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1)))
    (t : _root_.stdSimplex ℝ (Fin (n + 1))) :
    X.toSSetObjEquiv _ (singularAffinePull σ v) t =
      X.toSSetObjEquiv _ σ (affineSimplexMap v t) := by
  simp [singularAffinePull]

/-- Every affine subsimplex remains in the original singular simplex's image. -/
theorem singularAffinePull_range_subset {X : TopCat.{u}} {n m : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋m⦌))
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1))) :
    Set.range (X.toSSetObjEquiv _ (singularAffinePull σ v)) ⊆
      Set.range (X.toSSetObjEquiv _ σ) := by
  rintro _ ⟨t, rfl⟩
  exact ⟨affineSimplexMap v t, (singularAffinePull_apply σ v t).symm⟩

/-- Affine subdivision preserves membership in every small-singular subcomplex. -/
theorem singularAffinePull_mem {X : TopCat.{u}} {ι : Type v} (U : ι → Set X)
    {n m : ℕ} (σ : (TopCat.toSSet.obj X).obj (op ⦋m⦌))
    (hσ : σ ∈ (singularSmallSubcomplex X U).obj (op ⦋m⦌))
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1))) :
    singularAffinePull σ v ∈ (singularSmallSubcomplex X U).obj (op ⦋n⦌) := by
  obtain ⟨i, hi⟩ := hσ
  refine ⟨i, fun t => ?_⟩
  rw [singularAffinePull_apply]
  exact hi (affineSimplexMap v t)

/-- The barycenter of the first k+1 vertices in a permutation ordering. -/
def prefixBarycenter {n : ℕ} (p : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    _root_.stdSimplex ℝ (Fin (n + 1)) :=
  _root_.stdSimplex.map (fun j : Fin (k.val + 1) =>
    p ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩)
      (_root_.stdSimplex.barycenter : _root_.stdSimplex ℝ (Fin (k.val + 1)))

/-- An actual oriented barycentric subsimplex of the standard simplex. -/
def barycentricCell {n : ℕ} (p : Equiv.Perm (Fin (n + 1))) :
    C(_root_.stdSimplex ℝ (Fin (n + 1)), _root_.stdSimplex ℝ (Fin (n + 1))) :=
  affineSimplexMap (prefixBarycenter p)

/-- The singular simplex supported on one actual barycentric cell. -/
def singularBarycentricCell {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) (p : Equiv.Perm (Fin (n + 1))) :
    (TopCat.toSSet.obj X).obj (op ⦋n⦌) :=
  singularAffinePull σ (prefixBarycenter p)

theorem singularBarycentricCell_mem {X : TopCat.{u}} {ι : Type v} (U : ι → Set X)
    {n : ℕ} (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hσ : σ ∈ (singularSmallSubcomplex X U).obj (op ⦋n⦌))
    (p : Equiv.Perm (Fin (n + 1))) :
    singularBarycentricCell σ p ∈ (singularSmallSubcomplex X U).obj (op ⦋n⦌) :=
  singularAffinePull_mem U σ hσ (prefixBarycenter p)

end Sharpness.RealizationUnitHomology
