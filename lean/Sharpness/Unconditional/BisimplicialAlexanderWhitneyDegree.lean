import Sharpness.AlexanderWhitneyFaces
import Sharpness.ChainTotalProjection

/-! The actual degree maps of Alexander–Whitney, with the prescribed
front/back-face components. No chain-map or quasi-isomorphism input occurs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Simplicial Opposite

variable (X : SimplicialObject SSet.{u}) (R : Type u) [CommRing R]

/-- The finite sum of all front/back components in a fixed total degree. -/
def bisimplicialAlexanderWhitneyDegree (n : ℕ) :
    (bisimplicialDiagonalChains X R).X n ⟶ (bisimplicialTotalChains X R).X n :=
  Sigma.desc fun x => ∑ i : Fin (n + 1),
    (X.obj (op ⦋i.val⦌)).ιChainComplex
      (alexanderWhitneySimplex X i.val (n - i.val) n (by omega) x) ≫
        (bisimplicialChainBicomplex X R).ιTotal (ComplexShape.down ℕ)
          i.val (n - i.val) n (by change i.val + (n - i.val) = n; omega)

@[reassoc]
theorem bisimplicialAlexanderWhitneyDegree_simplex (n : ℕ)
    (x : (bisimplicialDiagonal X).obj (op ⦋n⦌)) :
    (bisimplicialDiagonal X).ιChainComplex (R := ModuleCat.of R R) x ≫
        bisimplicialAlexanderWhitneyDegree X R n =
      ∑ i : Fin (n + 1),
        (X.obj (op ⦋i.val⦌)).ιChainComplex
          (alexanderWhitneySimplex X i.val (n - i.val) n (by omega) x) ≫
            (bisimplicialChainBicomplex X R).ιTotal (ComplexShape.down ℕ)
              i.val (n - i.val) n (by change i.val + (n - i.val) = n; omega) :=
  Sigma.ι_desc _ _

/-- Every actual summand projection has exactly the manuscript's face formula. -/
theorem bisimplicialAlexanderWhitneyDegree_component (p q n : ℕ)
    (h : p + q = n) (x : (bisimplicialDiagonal X).obj (op ⦋n⦌)) :
    (bisimplicialDiagonal X).ιChainComplex (R := ModuleCat.of R R) x ≫
        bisimplicialAlexanderWhitneyDegree X R n ≫
          chainTotalProjection (bisimplicialChainBicomplex X R) p q n h =
      (X.obj (op ⦋p⦌)).ιChainComplex (alexanderWhitneySimplex X p q n h x) := by
  classical
  rw [← Category.assoc, bisimplicialAlexanderWhitneyDegree_simplex, sum_comp]
  let k : Fin (n + 1) := ⟨p, by omega⟩
  rw [Finset.sum_eq_single k]
  · have hq : n - p = q := by omega
    subst q
    dsimp only [k]
    simp only [Category.assoc]
    rw [chainTotalProjection_inclusion (bisimplicialChainBicomplex X R)]
    exact Category.comp_id _
  · intro i _ hi
    have hip : i.val ≠ p := by
      intro he
      apply hi
      exact Fin.ext he
    rw [Category.assoc, chainTotalProjection_other _ p q n i.val (n - i.val)
      h (by omega) hip, comp_zero]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

end Sharpness
