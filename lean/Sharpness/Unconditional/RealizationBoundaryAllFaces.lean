import Sharpness.Unconditional.RealizationBoundaryFaceRealization
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-! The actual coordinate identification for all simplex faces, including the
empty face. Compatibility is always with the actual ambient inclusion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.RealizationBoundary
open CategoryTheory Simplicial Opposite

instance emptyFaceSimplex_isEmpty (n : ℕ) (m : SimplexCategoryᵒᵖ) :
    IsEmpty ((SSet.stdSimplex.face.{u} (∅ : Finset (Fin (n + 1)))).toSSet.obj m) := by
  constructor
  intro x
  have h : Finset.image (SSet.stdSimplex.objEquiv x.val).toOrderHom Finset.univ ⊆ ∅ := x.property
  simpa using h (Finset.mem_image_of_mem _ (Finset.mem_univ 0))

def emptyFaceSingularMap (n : ℕ) :
    (SSet.stdSimplex.face.{u} (∅ : Finset (Fin (n + 1)))).toSSet ⟶
      TopCat.toSSet.obj (TopCat.of PEmpty.{u + 1}) where
  app m := ↾fun x => isEmptyElim x
  naturality {m l} f := by
    ext x
    exact isEmptyElim x

instance emptyFaceRealization_isEmpty (n : ℕ) :
    IsEmpty |(SSet.stdSimplex.face.{u} (∅ : Finset (Fin (n + 1)))).toSSet| := by
  constructor
  intro x
  exact ((sSetTopAdj.homEquiv _ _).symm (emptyFaceSingularMap n) x).elim

instance emptyCoordinateFace_isEmpty (n : ℕ) :
    IsEmpty (finiteCoordinateFace.{u} (∅ : Finset (Fin (n + 1)))) := by
  constructor
  intro t
  have hall (j : Fin (n + 1)) : (t.val.down : Simplex n).val j = 0 := t.property j (by simp)
  have hs := _root_.stdSimplex.sum_eq_one (t.val.down : Simplex n)
  change (∑ j : Fin (n + 1), (t.val.down : Simplex n).val j) = 1 at hs
  simp only [hall, Finset.sum_const_zero] at hs
  exact zero_ne_one hs

def faceHomeo {n : ℕ} (S : Finset (Fin (n + 1))) :
    |(SSet.stdSimplex.face.{u} S).toSSet| ≃ₜ finiteCoordinateFace.{u} S := by
  classical
  by_cases hS : S.Nonempty
  · exact representedFaceHomeo S
      (S.orderIsoOfFin (show S.card = (S.card - 1) + 1 by
        have := Finset.card_pos.mpr hS
        omega))
  · have h : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    exact Homeomorph.empty

theorem faceHomeo_inclusion {n : ℕ} (S : Finset (Fin (n + 1)))
    (x : |(SSet.stdSimplex.face.{u} S).toSSet|) :
    (faceHomeo S x).val =
      (SSet.toTopSimplex.app ⦋n⦌).hom (SSet.toTop.map (SSet.stdSimplex.face S).ι x) := by
  classical
  unfold faceHomeo
  split_ifs with hS
  · exact representedFaceHomeo_inclusion S _ x
  · have h : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    exact isEmptyElim x

theorem isClosed_finiteCoordinateFace {n : ℕ} (S : Finset (Fin (n + 1))) :
    IsClosed (finiteCoordinateFace.{u} S) := by
  have h : finiteCoordinateFace.{u} S = ⋂ j, ⋂ (_ : j ∉ S),
      {t | (t.down : Simplex n).val j = 0} := by
    ext t
    simp [finiteCoordinateFace]
  rw [h]
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  change IsClosed (setOf (fun t : ULift.{u} (Simplex n) => t.down.val j = 0))
  exact isClosed_eq (((continuous_apply j).comp continuous_subtype_val).comp
    continuous_uliftDown) continuous_const

end Sharpness.RealizationBoundary
