import Sharpness.Unconditional.BisimplicialAlexanderWhitneyChain
import Sharpness.ChainTotalProjectionNaturality

/-! Naturality of the constructed Alexander–Whitney map in arbitrary
bisimplicial sets, for the actual diagonal and total chain maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

variable {X Y : SimplicialObject SSet.{u}} (φ : X ⟶ Y)
    (R : Type u) [CommRing R]

def bisimplicialDiagonalMap : bisimplicialDiagonal X ⟶ bisimplicialDiagonal Y :=
  Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ) (Functor.uncurry.map φ)

def bisimplicialDiagonalChainsMap :
    bisimplicialDiagonalChains X R ⟶ bisimplicialDiagonalChains Y R :=
  SSet.chainComplexMap (bisimplicialDiagonalMap φ) (ModuleCat.of R R)

def bisimplicialChainBicomplexMap : bisimplicialChainBicomplex X R ⟶
    bisimplicialChainBicomplex Y R :=
  (AlgebraicTopology.alternatingFaceMapComplex (ChainComplex (ModuleCat.{u} R) ℕ)).map
    (Functor.whiskerRight φ (simplicialChainsFunctor R))

def bisimplicialTotalChainsMap : bisimplicialTotalChains X R ⟶ bisimplicialTotalChains Y R :=
  HomologicalComplex₂.total.map (bisimplicialChainBicomplexMap φ R) (ComplexShape.down ℕ)

theorem alexanderWhitneySimplex_naturality (p q n : ℕ) (h : p + q = n)
    (x : (bisimplicialDiagonal X).obj (op ⦋n⦌)) :
    (φ.app (op ⦋p⦌)).app (op ⦋q⦌) (alexanderWhitneySimplex X p q n h x) =
      alexanderWhitneySimplex Y p q n h
        ((φ.app (op ⦋n⦌)).app (op ⦋n⦌) x) := by
  rw [alexanderWhitneySimplex_eq_pull, alexanderWhitneySimplex_eq_pull]
  exact congrArg (fun z => z x) ((Functor.uncurry.map φ).naturality
    (show (op ⦋n⦌, op ⦋n⦌) ⟶ (op ⦋p⦌, op ⦋q⦌) from
      ((alexanderWhitneyFront p q n h).op, (alexanderWhitneyBack p q n h).op)))

/-- Strict naturality for the actual constructed chain map. -/
theorem bisimplicialAlexanderWhitney_naturality :
    bisimplicialDiagonalChainsMap φ R ≫ bisimplicialAlexanderWhitney Y R =
      bisimplicialAlexanderWhitney X R ≫ bisimplicialTotalChainsMap φ R := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply SSet.chainComplex_hom_ext
  intro x
  apply chainTotal_projection_hom_ext (bisimplicialChainBicomplex Y R)
  intro p q h
  simp only [HomologicalComplex.comp_f, Category.assoc]
  have hD := SSet.ι_chainComplexMap_f _ _ (bisimplicialDiagonalMap φ) (ModuleCat.of R R) x
  have hT := chainTotalMap_projection (bisimplicialChainBicomplex X R)
    (bisimplicialChainBicomplex Y R) (bisimplicialChainBicomplexMap φ R) p q n h
  have hC := SSet.ι_chainComplexMap_f _ _ (φ.app (op ⦋p⦌)) (ModuleCat.of R R)
    (alexanderWhitneySimplex X p q n h x)
  change (bisimplicialDiagonal X).ιChainComplex x ≫
    (bisimplicialDiagonalChainsMap φ R).f n =
      (bisimplicialDiagonal Y).ιChainComplex
        ((φ.app (op ⦋n⦌)).app (op ⦋n⦌) x) at hD
  change (bisimplicialTotalChainsMap φ R).f n ≫ _ = _ at hT
  change (X.obj (op ⦋p⦌)).ιChainComplex _ ≫
    ((bisimplicialChainBicomplexMap φ R).f p).f q = _ at hC
  calc
    _ = (bisimplicialDiagonal Y).ιChainComplex
          ((φ.app (op ⦋n⦌)).app (op ⦋n⦌) x) ≫
        (bisimplicialAlexanderWhitney Y R).f n ≫
          chainTotalProjection (bisimplicialChainBicomplex Y R) p q n h := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ (bisimplicialAlexanderWhitney Y R).f n ≫
          chainTotalProjection (bisimplicialChainBicomplex Y R) p q n h) hD
    _ = (Y.obj (op ⦋p⦌)).ιChainComplex
        (alexanderWhitneySimplex Y p q n h
          ((φ.app (op ⦋n⦌)).app (op ⦋n⦌) x)) :=
      bisimplicialAlexanderWhitney_component Y R p q n h _
    _ = (Y.obj (op ⦋p⦌)).ιChainComplex
        ((φ.app (op ⦋p⦌)).app (op ⦋q⦌) (alexanderWhitneySimplex X p q n h x)) := by
      rw [alexanderWhitneySimplex_naturality]
    _ = (X.obj (op ⦋p⦌)).ιChainComplex
        (alexanderWhitneySimplex X p q n h x) ≫
          ((bisimplicialChainBicomplexMap φ R).f p).f q := hC.symm
    _ = ((bisimplicialDiagonal X).ιChainComplex x ≫
        (bisimplicialAlexanderWhitney X R).f n ≫
          chainTotalProjection (bisimplicialChainBicomplex X R) p q n h) ≫
            ((bisimplicialChainBicomplexMap φ R).f p).f q :=
      congrArg (fun f => f ≫ ((bisimplicialChainBicomplexMap φ R).f p).f q)
        (bisimplicialAlexanderWhitney_component X R p q n h x).symm
    _ = _ := by rw [Category.assoc, Category.assoc, ← hT]

end Sharpness
