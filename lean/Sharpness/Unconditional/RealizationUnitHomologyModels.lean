import Sharpness.Unconditional.RealizationUnitHomologySimplex

/-! Positive-degree exactness on the actual topological simplex models used by
the native singular-chain evaluation adjunction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.RealizationUnitHomology
open CategoryTheory Simplicial

theorem topologicalSimplex_contractible (n : SimplexCategory) :
    ContractibleSpace (SimplexCategory.toTop.{u}.obj n) := by
  letI : ContractibleSpace ((SSet.stdSimplex.{u} ⋙ SSet.toTop).obj n) :=
    standardSimplex_contractible.{u} n
  exact (TopCat.homeoOfIso (SSet.toTopSimplex.{u}.app n)).symm.contractibleSpace

/-- The actual singular chains on each topological model simplex are exact
in every positive degree, for any commutative coefficient ring. -/
theorem topologicalSimplex_chains_exactAt (R : Type u) [CommRing R]
    (n : SimplexCategory) (k : ℕ) (hk : k ≠ 0) :
    ((SingularCohomology.chainsFunctor R).obj (SimplexCategory.toTop.{u}.obj n)).ExactAt k := by
  letI := topologicalSimplex_contractible.{u} n
  let f := SimplexCategory.toTop.{u}.map (SimplexCategory.isTerminalZero.from n)
  let e := contractibleToPointChains R f
  letI := e.quasiIso_hom
  apply (exactAt_iff_of_quasiIsoAt e.hom k).mpr
  exact AlgebraicTopology.singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace
    (ModuleCat.{u} R) k (ModuleCat.of R R) (SimplexCategory.toTop.{u}.obj ⦋0⦌) hk

end Sharpness.RealizationUnitHomology
