import Sharpness.Unconditional.RealizationSubdivisionMeshIterates

/-! Eventual smallness of actual iterated barycentric singular simplices,
uniformly over all permutation choices and every subsequent depth. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace Sharpness.RealizationUnitHomology
open CategoryTheory Simplicial Opposite

def singularIteratedBarycentricCell {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (ps : List (Equiv.Perm (Fin (n + 1)))) :
    (TopCat.toSSet.obj X).obj (op ⦋n⦌) :=
  (X.toSSetObjEquiv _).symm ((X.toSSetObjEquiv _ σ).comp (iteratedBarycentricCell ps))

@[simp] theorem singularIteratedBarycentricCell_apply {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (ps : List (Equiv.Perm (Fin (n + 1))))
    (t : _root_.stdSimplex ℝ (Fin (n + 1))) :
    X.toSSetObjEquiv _ (singularIteratedBarycentricCell σ ps) t =
      X.toSSetObjEquiv _ σ (iteratedBarycentricCell ps t) := by
  simp [singularIteratedBarycentricCell]

@[simp] theorem singularIteratedBarycentricCell_nil {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) : singularIteratedBarycentricCell σ [] = σ := by
  apply (X.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  simp

theorem singularIteratedBarycentricCell_cons {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) (p : Equiv.Perm (Fin (n + 1)))
    (ps : List (Equiv.Perm (Fin (n + 1)))) :
    singularIteratedBarycentricCell σ (p :: ps) =
      singularBarycentricCell (singularIteratedBarycentricCell σ ps) p := by
  apply (X.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  simp only [singularIteratedBarycentricCell_apply, singularBarycentricCell,
    singularAffinePull_apply, iteratedBarycentricCell_cons, ContinuousMap.comp_apply,
    barycentricCell]

/-- Only the image of the given simplex must be covered. No separation or
metric assumption on X is needed. The output is native small-subcomplex membership. -/
theorem singularIteratedBarycentricCell_eventually_small {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) {ι : Type v}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ t, ∃ i, X.toSSetObjEquiv _ σ t ∈ U i) :
    ∃ N : ℕ, ∀ ps : List (Equiv.Perm (Fin (n + 1))), N ≤ ps.length →
      singularIteratedBarycentricCell σ ps ∈
        (singularSmallSubcomplex X U).obj (op ⦋n⦌) := by
  obtain ⟨N, hN⟩ := iteratedBarycentricCell_eventually_small_comp
    (X.toSSetObjEquiv _ σ) U hU hcover
  refine ⟨N, fun ps hps => ?_⟩
  obtain ⟨i, hi⟩ := hN ps hps
  refine ⟨i, fun t => ?_⟩
  rw [singularIteratedBarycentricCell_apply]
  exact hi (Set.mem_range_self t)

end Sharpness.RealizationUnitHomology
