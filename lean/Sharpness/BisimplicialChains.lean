import Sharpness.SimplicialReplacementLinearization
import Mathlib.Algebra.Homology.TotalComplex

/-! Actual diagonal and iterated alternating-face chains of an
arbitrary bisimplicial set. These definitions do not involve fusion
systems, homotopy colimits, or any comparison assumption. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable (X : SimplicialObject SSet.{u}) (R : Type u) [CommRing R]

def bisimplicialDiagonal : SSet.{u} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj X

def bisimplicialChainBicomplex :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (AlgebraicTopology.alternatingFaceMapComplex (ChainComplex (ModuleCat.{u} R) ℕ)).obj
    (X ⋙ simplicialChainsFunctor R)

def bisimplicialTotalChains : ChainComplex (ModuleCat.{u} R) ℕ :=
  (bisimplicialChainBicomplex X R).total (ComplexShape.down ℕ)

def bisimplicialDiagonalChains : ChainComplex (ModuleCat.{u} R) ℕ :=
  (bisimplicialDiagonal X).chainComplex (ModuleCat.of R R)

end Sharpness
