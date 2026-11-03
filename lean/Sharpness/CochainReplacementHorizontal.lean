import Sharpness.CategoryCochainReplacement
import Sharpness.CoefficientReplacement
import Sharpness.ProductCochainHomologyNaturality
import Sharpness.AlternatingCofaceFunctorIso

/-! Taking the actual vertical cohomology of the replacement diagram
produces the actual coefficient cosimplicial object, naturally for all
order maps. Its alternating complex is therefore the actual horizontal
cohomology complex, including the differential. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (D : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ)

def cochainReplacementCohomologyNatIso (q : ℕ) :
    cochainReplacement D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q ≅
      coefficientReplacement
        (D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q) :=
  NatIso.ofComponents
    (fun i => productCochainsHomologyIso
      (fun s : ComposableArrows C i.len => D.obj (op (chainHead s))) q)
    (fun {i j} f => productCochainsHomologyIso_naturality
      (fun s : ComposableArrows C i.len => D.obj (op (chainHead s)))
      (fun s : ComposableArrows C j.len => D.obj (op (chainHead s)))
      (restrictCategoryChain f) (fun s => D.map (categoryChainHeadArrow f s).op) q)

def cochainReplacementHorizontalIso (q : ℕ) :
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (cochainReplacementBicomplex D) ≅
      coefficientCochains (D ⋙ HomologicalComplex.homologyFunctor
        (ModuleCat.{u} R) (ComplexShape.up ℕ) q) :=
  alternatingCofaceFunctorIso
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q)
      (cochainReplacement D) ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u} R)).mapIso
      (cochainReplacementCohomologyNatIso D q)

end Sharpness
