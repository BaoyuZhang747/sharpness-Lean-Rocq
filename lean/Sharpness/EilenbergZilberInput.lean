import Sharpness.AlexanderWhitneyFaces
import Sharpness.ChainTotalProjection
import Mathlib.Algebra.Homology.QuasiIso

/-! Uniform literature input: Weibel, An Introduction to Homological
Algebra, Theorem 8.5.1 and Section 8.5.4, printed pp.276–278.
The Alexander–Whitney map is specified by every actual front/back
face component and is a quasi-isomorphism for any bisimplicial set.
This record contains no fusion system, coefficient module A,
augmentation, realization, spectral sequence, or sharpness conclusion.
See sources/EilenbergZilberReferences.* for the exact boundary. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite

structure EilenbergZilberInput (R : Type u) [CommRing R] where
  alexanderWhitney : ∀ X : SimplicialObject SSet.{u},
    bisimplicialDiagonalChains X R ⟶ bisimplicialTotalChains X R
  alexanderWhitney_component : ∀ (X : SimplicialObject SSet.{u}) (p q n : ℕ)
    (h : p+q=n) (x : (bisimplicialDiagonal X).obj (op ⦋n⦌)),
    (bisimplicialDiagonal X).ιChainComplex (R := ModuleCat.of R R) x ≫
        (alexanderWhitney X).f n ≫
          chainTotalProjection (bisimplicialChainBicomplex X R) p q n h =
      (X.obj (op ⦋p⦌)).ιChainComplex (alexanderWhitneySimplex X p q n h x)
  Weibel_8_5_1 : ∀ X, QuasiIso (alexanderWhitney X)

theorem alexanderWhitney_zeroColumn_component {R : Type u} [CommRing R]
    (ez : EilenbergZilberInput.{u} R) (X : SimplicialObject SSet.{u})
    (n : ℕ) (h : 0+n=n) (x : (bisimplicialDiagonal X).obj (op ⦋n⦌)) :
    (bisimplicialDiagonal X).ιChainComplex (R := ModuleCat.of R R) x ≫
        (ez.alexanderWhitney X).f n ≫
          chainTotalProjection (bisimplicialChainBicomplex X R) 0 n n h =
      (X.obj (op ⦋0⦌)).ιChainComplex
        ((X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op).app (op ⦋n⦌) x) := by
  rw [ez.alexanderWhitney_component, alexanderWhitneySimplex_zero]

end Sharpness
