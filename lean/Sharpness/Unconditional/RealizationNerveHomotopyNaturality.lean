import Sharpness.Unconditional.RealizationNerveHomotopyGluing
import Sharpness.Unconditional.RealizationPrismNaturalityCells

/-! Simplicial compatibility of the lifted geometric prism staircases. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.RealizationPrism
open CategoryTheory Simplicial Opposite MonoidalCategory

/-- The lifted staircase, bundled as an actual simplex-category morphism. -/
def staircaseMap {n m : ℕ} (a : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    ⦋n + 1⦌ ⟶ ⦋m + 1⦌ :=
  SimplexCategory.mkHom (staircaseLift a.toOrderHom i)

theorem staircaseMap_comp_sigma {n m : ℕ} (a : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    staircaseMap a i ≫ SimplexCategory.σ (a.toOrderHom i) = SimplexCategory.σ i ≫ a := by
  ext k
  exact congrArg Fin.val (staircaseLift_predAbove a.toOrderHom i k)

theorem staircaseMap_interval {n m : ℕ} (a : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    (Δ[1] : SSet.{u}).map (staircaseMap a i).op
        (SSet.stdSimplex.objMk₁ (a.toOrderHom i).succ.castSucc) =
      SSet.stdSimplex.objMk₁ i.succ.castSucc := by
  ext k : 1
  change SSet.stdSimplex.objMk₁.{u} (a.toOrderHom i).succ.castSucc
      (staircaseLift a.toOrderHom i k) = SSet.stdSimplex.objMk₁.{u} i.succ.castSucc k
  simp only [SSet.stdSimplex.objMk₁_apply, Fin.castSucc_lt_castSucc_iff]
  simp only [staircaseLift_lt_succ]
  simp only [← Fin.le_castSucc_iff]

/-- The actual simplex of a simplicial homotopy commutes with the staircase lift. -/
theorem staircase_homotopy_simplex {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) {n m : ℕ} (a : ⦋n⦌ ⟶ ⦋m⦌)
    (i : Fin (n + 1)) (x : X.obj (op ⦋m⦌)) :
    Y.map (staircaseMap a i).op
        (H.h.app _ (X.σ (a.toOrderHom i) x,
          SSet.stdSimplex.objMk₁ (a.toOrderHom i).succ.castSucc)) =
      H.h.app _ (X.σ i (X.map a.op x), SSet.stdSimplex.objMk₁ i.succ.castSucc) := by
  rw [← NatTrans.naturality_apply]
  apply congrArg (H.h.app _)
  apply Prod.ext
  · change X.map (staircaseMap a i).op (X.map (SimplexCategory.σ (a.toOrderHom i)).op x) =
      X.map (SimplexCategory.σ i).op (X.map a.op x)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      staircaseMap_comp_sigma]
  · exact staircaseMap_interval a i

/-- The continuous geometric prism is natural under every simplex map,
including all face and degeneracy maps. -/
theorem simplexRealizationPrism_naturality {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) {n m : ℕ} (a : ⦋n⦌ ⟶ ⦋m⦌)
    (x : X.obj (op ⦋m⦌)) (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 1))) :
    simplexRealizationPrism H (X.map a.op x) (t, z) =
      simplexRealizationPrism H x (t, stdSimplex.map a z) := by
  obtain ⟨i, hi⟩ := mem_some_cell (t, z)
  have hj := map_mem_cell a.toOrderHom i (t, z) hi
  have hs := simplexRealizationPrism_on_cell H (X.map a.op x) i ⟨(t, z), hi⟩
  have ht := simplexRealizationPrism_on_cell H x (a.toOrderHom i)
    ⟨(t, stdSimplex.map a z), hj⟩
  have hc : stdSimplex.map (staircaseMap a i) (cellSimplex i ⟨(t, z), hi⟩) =
      cellSimplex (a.toOrderHom i) ⟨(t, stdSimplex.map a z), hj⟩ :=
    map_cellSimplex_staircaseLift a.toOrderHom i ⟨(t, z), hi⟩
  rw [hs, ht]
  change realizationSimplex _ (cellSimplex i ⟨(t, z), hi⟩) =
    realizationSimplex _ (cellSimplex (a.toOrderHom i) ⟨(t, stdSimplex.map a z), hj⟩)
  rw [← hc]
  rw [← realizationSimplex_naturality, staircase_homotopy_simplex]

end Sharpness.RealizationPrism
