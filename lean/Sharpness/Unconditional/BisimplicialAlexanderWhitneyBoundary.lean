import Sharpness.Unconditional.BisimplicialAlexanderWhitneySimplexFaces
import Sharpness.Unconditional.BisimplicialAlexanderWhitneySigns

/-! The complete Alexander–Whitney boundary identity on simplex generators,
with arbitrary commutative-ring coefficients and in every degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Preadditive Simplicial Opposite

variable (X : SimplicialObject SSet.{u}) (R : Type u) [CommRing R]

theorem chainMap_sum_f {I : Type*} [Fintype I]
    {C D : ChainComplex (ModuleCat.{u} R) ℕ} (f : I → (C ⟶ D)) (q : ℕ) :
    (∑ i, f i).f q = ∑ i, (f i).f q :=
  map_sum (HomologicalComplex.Hom.fAddMonoidHom q) f Finset.univ

theorem bisimplicialAlexanderWhitney_boundary (p q n : ℕ) (h : p + q = n)
    (x : (bisimplicialDiagonal X).obj (op ⦋n + 1⦌)) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      (X.obj (op ⦋p⦌)).ιChainComplex (R := ModuleCat.of R R)
        (alexanderWhitneySimplex X p q n h ((bisimplicialDiagonal X).δ i x))) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val •
        (X.obj (op ⦋p⦌)).ιChainComplex
          ((X.map (SimplexCategory.δ i).op).app (op ⦋q⦌)
            (alexanderWhitneySimplex X (p + 1) q (n + 1) (by omega) x))) +
      (-1 : ℤ) ^ p •
        ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
          (X.obj (op ⦋p⦌)).ιChainComplex
            ((X.obj (op ⦋p⦌)).δ j
              (alexanderWhitneySimplex X p (q + 1) (n + 1) (by omega) x)) := by
  apply alexanderWhitney_alternating_split p q n h
  · intro i
    rw [alexanderWhitneySimplex_face_early X p q n h]
  · intro j
    rw [alexanderWhitneySimplex_face_late X p q n h]
  · rw [alexanderWhitneySimplex_face_middle X p q n h]

/-- The horizontal native alternating-face differential evaluated on a simplex. -/
theorem bisimplicial_horizontal_boundary (p q : ℕ)
    (x : (X.obj (op ⦋p + 1⦌)).obj (op ⦋q⦌)) :
    (X.obj (op ⦋p + 1⦌)).ιChainComplex (R := ModuleCat.of R R) x ≫
        ((bisimplicialChainBicomplex X R).d (p + 1) p).f q =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val •
        (X.obj (op ⦋p⦌)).ιChainComplex
          ((X.map (SimplexCategory.δ i).op).app (op ⦋q⦌) x) := by
  change _ ≫ (((AlgebraicTopology.alternatingFaceMapComplex
    (ChainComplex (ModuleCat.{u} R) ℕ)).obj (X ⋙ simplicialChainsFunctor R)).d
      (p + 1) p).f q = _
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  simp only [AlgebraicTopology.AlternatingFaceMapComplex.objD,
    chainMap_sum_f, HomologicalComplex.zsmul_f_apply, comp_sum, comp_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact SSet.ι_chainComplexMap_f _ _ (X.map (SimplexCategory.δ i).op) (ModuleCat.of R R) x

end Sharpness
