import Sharpness.Unconditional.RealizationUnitHomologySubdivisionFaces

/-! Actual outer faces of subdivision cells, with an explicit monotone
complement equation. The permutation reindexing supplies that equation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.RealizationUnitHomology
open Simplicial Opposite

/-- A prefix not containing the final vertex lies in its literal ambient face. -/
theorem prefixBarycenter_outer_face {n : ℕ}
    (p : Equiv.Perm (Fin (n + 2))) (q : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 2))
    (hp : ∀ k : Fin (n + 1), p k.castSucc = i.succAbove (q k))
    (k : Fin (n + 1)) :
    prefixBarycenter p k.castSucc =
      _root_.stdSimplex.map i.succAbove (prefixBarycenter q k) := by
  unfold prefixBarycenter
  rw [_root_.stdSimplex.map_comp_apply]
  congr 1
  funext a
  exact hp ⟨a.val, lt_of_lt_of_le a.isLt (Nat.succ_le_of_lt k.isLt)⟩

/-- The outer face of a cell is the smaller-dimensional cell in the omitted face. -/
theorem barycentricCell_outer_face {n : ℕ}
    (p : Equiv.Perm (Fin (n + 2))) (q : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 2))
    (hp : ∀ k : Fin (n + 1), p k.castSucc = i.succAbove (q k)) :
    (barycentricCell p).comp
        ⟨_root_.stdSimplex.map (Fin.last (n + 1)).succAbove,
          _root_.stdSimplex.continuous_map (Fin.last (n + 1)).succAbove⟩ =
      (⟨_root_.stdSimplex.map i.succAbove,
          _root_.stdSimplex.continuous_map i.succAbove⟩ :
        C(_root_.stdSimplex ℝ (Fin (n + 1)), _root_.stdSimplex ℝ (Fin (n + 2)))).comp
          (barycentricCell q) := by
  rw [barycentricCell, affineSimplexMap_index, stdSimplex_map_eq_affine,
    barycentricCell, affineSimplexMap_comp]
  congr 1
  funext k
  simp only [Fin.succAbove_last]
  rw [prefixBarycenter_outer_face p q i hp k]
  exact congrArg (fun f => f (prefixBarycenter q k)) (stdSimplex_map_eq_affine i.succAbove)

/-- The same outer-face identity in the actual singular simplicial set. -/
theorem singularBarycentricCell_outer_face {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌))
    (p : Equiv.Perm (Fin (n + 2))) (q : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 2))
    (hp : ∀ k : Fin (n + 1), p k.castSucc = i.succAbove (q k)) :
    (TopCat.toSSet.obj X).δ (Fin.last (n + 1)) (singularBarycentricCell σ p) =
      singularBarycentricCell ((TopCat.toSSet.obj X).δ i σ) q := by
  apply (X.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  simp only [TopCat.toSSetObjEquiv_δ_apply, singularBarycentricCell,
    singularAffinePull_apply]
  apply congrArg (X.toSSetObjEquiv _ σ)
  exact congrArg (fun f => f t) (barycentricCell_outer_face p q i hp)

end Sharpness.RealizationUnitHomology
