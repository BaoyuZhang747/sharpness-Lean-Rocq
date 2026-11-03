import Sharpness.Unconditional.BisimplicialAlexanderWhitneyDegree
import Sharpness.Unconditional.BisimplicialAlexanderWhitneyBoundary
import Sharpness.Unconditional.ChainTotalIncomingProjections

/-! The actual Alexander–Whitney chain map, constructed from its finite
front/back-face degree maps and the proved boundary identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits Simplicial Opposite

variable (X : SimplicialObject SSet.{u}) (R : Type u) [CommRing R]

theorem bisimplicialAlexanderWhitneyDegree_d_component (p q n : ℕ) (h : p + q = n)
    (x : (bisimplicialDiagonal X).obj (op ⦋n + 1⦌)) :
    (bisimplicialDiagonal X).ιChainComplex (R := ModuleCat.of R R) x ≫
        bisimplicialAlexanderWhitneyDegree X R (n + 1) ≫
          (bisimplicialTotalChains X R).d (n + 1) n ≫
            chainTotalProjection (bisimplicialChainBicomplex X R) p q n h =
      ((X.obj (op ⦋p + 1⦌)).ιChainComplex
          (alexanderWhitneySimplex X (p + 1) q (n + 1) (by omega) x) ≫
        ((bisimplicialChainBicomplex X R).d (p + 1) p).f q) +
      (-1 : ℤ) ^ p •
        ((X.obj (op ⦋p⦌)).ιChainComplex
            (alexanderWhitneySimplex X p (q + 1) (n + 1) (by omega) x) ≫
          ((bisimplicialChainBicomplex X R).X p).d (q + 1) q) := by
  let K := bisimplicialChainBicomplex X R
  have hh := congrArg (fun f => f ≫ (K.d (p + 1) p).f q)
    (bisimplicialAlexanderWhitneyDegree_component X R (p + 1) q (n + 1) (by omega) x)
  have hv := congrArg (fun f => f ≫ (K.X p).d (q + 1) q)
    (bisimplicialAlexanderWhitneyDegree_component X R p (q + 1) (n + 1) (by omega) x)
  simp only [Category.assoc] at hh hv
  change _ ≫ _ ≫ (K.D₁ (ComplexShape.down ℕ) (n + 1) n +
    K.D₂ (ComplexShape.down ℕ) (n + 1) n) ≫ _ = _
  rw [add_comp, chainTotal_horizontal_incoming K p q n h,
    chainTotal_vertical_incoming K p q n h]
  simp only [comp_add, Linear.comp_units_smul, Category.assoc, Units.smul_def,
    Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, comp_zsmul, zsmul_comp]
  rw [hh, hv]

theorem bisimplicialAlexanderWhitneyDegree_comm (n : ℕ) :
    bisimplicialAlexanderWhitneyDegree X R (n + 1) ≫
        (bisimplicialTotalChains X R).d (n + 1) n =
      (bisimplicialDiagonalChains X R).d (n + 1) n ≫
        bisimplicialAlexanderWhitneyDegree X R n := by
  apply SSet.chainComplex_hom_ext
  intro x
  apply chainTotal_projection_hom_ext (bisimplicialChainBicomplex X R)
  intro p q h
  simp only [Category.assoc]
  rw [bisimplicialAlexanderWhitneyDegree_d_component]
  rw [bisimplicial_horizontal_boundary]
  have hv := (X.obj (op ⦋p⦌)).ιChainComplex_d (R := ModuleCat.of R R)
    (alexanderWhitneySimplex X p (q + 1) (n + 1) (by omega) x)
  change (X.obj (op ⦋p⦌)).ιChainComplex _ ≫
    ((bisimplicialChainBicomplex X R).X p).d (q + 1) q = _ at hv
  rw [hv]
  have hd :
      (bisimplicialDiagonal X).ιChainComplex (R := ModuleCat.of R R) x ≫
          (bisimplicialDiagonalChains X R).d (n + 1) n ≫
            bisimplicialAlexanderWhitneyDegree X R n ≫
              chainTotalProjection (bisimplicialChainBicomplex X R) p q n h =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          (X.obj (op ⦋p⦌)).ιChainComplex
            (alexanderWhitneySimplex X p q n h ((bisimplicialDiagonal X).δ i x)) := by
    have hd0 := (bisimplicialDiagonal X).ιChainComplex_d (R := ModuleCat.of R R) x
    change (bisimplicialDiagonal X).ιChainComplex x ≫
      (bisimplicialDiagonalChains X R).d (n + 1) n = _ at hd0
    rw [← Category.assoc, ← Category.assoc, hd0]
    simp only [sum_comp, zsmul_comp, Category.assoc,
      bisimplicialAlexanderWhitneyDegree_component]
  rw [hd]
  exact (bisimplicialAlexanderWhitney_boundary X R p q n h x).symm

/-- The Alexander–Whitney chain map for every bisimplicial set over every
commutative coefficient ring, with all boundary identities proved. -/
def bisimplicialAlexanderWhitney :
    bisimplicialDiagonalChains X R ⟶ bisimplicialTotalChains X R :=
  ChainComplex.ofHom (bisimplicialAlexanderWhitneyDegree X R)
    (bisimplicialAlexanderWhitneyDegree_comm X R)

/-- Exact agreement with all components specified by `EilenbergZilberInput`. -/
theorem bisimplicialAlexanderWhitney_component (p q n : ℕ) (h : p + q = n)
    (x : (bisimplicialDiagonal X).obj (op ⦋n⦌)) :
    (bisimplicialDiagonal X).ιChainComplex (R := ModuleCat.of R R) x ≫
        (bisimplicialAlexanderWhitney X R).f n ≫
          chainTotalProjection (bisimplicialChainBicomplex X R) p q n h =
      (X.obj (op ⦋p⦌)).ιChainComplex (alexanderWhitneySimplex X p q n h x) :=
  bisimplicialAlexanderWhitneyDegree_component X R p q n h x

end Sharpness
