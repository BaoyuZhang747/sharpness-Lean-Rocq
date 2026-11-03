import Sharpness.Unconditional.RealizationUnitHomologyModelPresentation
import Sharpness.Unconditional.FunctorChainTransposition
import Sharpness.Unconditional.ModelwiseChainComparison

/-! Natural chain maps of actual singular chains which agree in degree zero
have an actual natural chain homotopy. Exactness is used only on standard
topological simplex models, where it has already been proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.RealizationUnitHomology
open CategoryTheory Simplicial

variable (R : Type u) [CommRing R]

/-- The natural comparison theorem for actual singular-chain endomorphisms. -/
def singularNaturalChainHomotopy
    (f g : SingularCohomology.chainsFunctor R ⟶ SingularCohomology.chainsFunctor R)
    (hzero : ∀ X, (f.app X).f 0 = (g.app X).f 0) :
    Homotopy (functorChainComplexMap f) (functorChainComplexMap g) :=
  AcyclicModels.modelwiseHomotopyOfDegreeZeroEq
    (fun n (_ : Unit) => SimplexCategory.toTop.{u}.obj ⦋n⦌)
    (singularDegreePresentation R) (functorChainComplexMap f) (functorChainComplexMap g)
    (fun n _ => topologicalSimplex_chains_exactAt R ⦋n + 1⦌ (n + 1) (by omega))
    (by apply CategoryTheory.NatTrans.ext; funext X; exact hzero X)

/-- Evaluate the natural comparison to an actual chain homotopy on any space. -/
def singularChainHomotopy
    (f g : SingularCohomology.chainsFunctor R ⟶ SingularCohomology.chainsFunctor R)
    (hzero : ∀ X, (f.app X).f 0 = (g.app X).f 0) (X : TopCat.{u}) :
    Homotopy (f.app X) (g.app X) :=
  ((evaluation TopCat.{u} (ModuleCat.{u} R)).obj X).mapHomotopy
    (singularNaturalChainHomotopy R f g hzero)

end Sharpness.RealizationUnitHomology
