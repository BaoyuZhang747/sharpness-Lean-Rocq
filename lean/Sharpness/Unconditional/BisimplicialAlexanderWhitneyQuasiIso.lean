import Sharpness.Unconditional.BisimplicialModelPresentations
import Sharpness.Unconditional.BisimplicialModelBoundary
import Sharpness.Unconditional.ModelwiseHomotopyEquivalence

/-! The actual Alexander–Whitney chain map is a natural chain homotopy
equivalence. Freeness and exactness are proved on concrete representable
models; no comparison theorem or spectral sequence is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Simplicial
open AcyclicModels

variable (R : Type u) [CommRing R]

def bisimplicialAlexanderWhitneyFunctorZeroIso :
    (bisimplicialDiagonalFunctorComplex R).X 0 ≅
      (bisimplicialTotalFunctorComplex R).X 0 :=
  NatIso.ofComponents (fun X => bisimplicialAlexanderWhitneyZeroIso X R)
    (fun φ => congrArg (fun f => f.f 0) (bisimplicialAlexanderWhitney_naturality φ R))

def bisimplicialAlexanderWhitneyFunctorHomotopyEquiv :
    HomotopyEquiv (bisimplicialDiagonalFunctorComplex R)
      (bisimplicialTotalFunctorComplex R) :=
  modelwiseHomotopyEquivalence
    (fun n (_ : Unit) => bisimplicialRepresentable n n)
    (fun n (i : Fin (n + 1)) => bisimplicialRepresentable i.val (n - i.val))
    (bisimplicialDiagonalFunctorComplexPresentation R)
    (bisimplicialTotalFunctorComplexPresentation R)
    (bisimplicialAlexanderWhitneyFunctorMap R)
    (bisimplicialAlexanderWhitneyFunctorZeroIso R) rfl
    (fun n _ => bisimplicialRepresentableDiagonal_exactAt R (n+1) (n+1) (n+1) (by omega))
    (fun n i => bisimplicialRepresentableTotal_exactAt R i.val (n+1-i.val) (n+1) (by omega))
    (fun n i => bisimplicialRepresentableDiagonal_exactAt R i.val (n+2-i.val) (n+1) (by omega))
    (fun i => bisimplicialRepresentable_boundary_of_total_boundary R i.val (1-i.val)
      ((bisimplicialTotalFunctorComplexPresentation R 1).generator i))

def bisimplicialAlexanderWhitneyHomotopyEquiv (X : SimplicialObject SSet.{u}) :
    HomotopyEquiv (bisimplicialDiagonalChains X R) (bisimplicialTotalChains X R) :=
  ((evaluation _ (ModuleCat.{u} R)).obj X).mapHomotopyEquiv
    (bisimplicialAlexanderWhitneyFunctorHomotopyEquiv R)

@[simp] theorem bisimplicialAlexanderWhitneyHomotopyEquiv_hom
    (X : SimplicialObject SSet.{u}) :
    (bisimplicialAlexanderWhitneyHomotopyEquiv R X).hom =
      bisimplicialAlexanderWhitney X R :=
  bisimplicialAlexanderWhitneyFunctorMap_evaluation R X

theorem bisimplicialAlexanderWhitney_quasiIso (X : SimplicialObject SSet.{u})
    (R : Type u) [CommRing R] : QuasiIso (bisimplicialAlexanderWhitney X R) := by
  rw [← bisimplicialAlexanderWhitneyHomotopyEquiv_hom R X]
  exact (bisimplicialAlexanderWhitneyHomotopyEquiv R X).quasiIso_hom

end Sharpness
