import Sharpness.LinkingSubgroupDiagram
import Sharpness.SingularCochainFunctor
import Sharpness.CategoryCochainReplacementLaws

/-! The literal double cochain complex of Corollary 4.1, with arbitrary
constant coefficients. Its spaces, strings and both differentials are
constructed objects. No spectral-sequence or convergence assertion is
included in this definition. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Opposite
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

def subgroupCochainDiagram : F.CentricOrbitᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  L.subgroupDiagram.op ⋙ SingularCohomology.cochainFunctor R A

def subgroupCohomologyDiagram (n : ℕ) : F.CentricOrbitᵒᵖ ⥤ ModuleCat.{u} R :=
  L.subgroupCochainDiagram R A ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n

def subgroupBicomplex :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  cochainReplacementBicomplex (L.subgroupCochainDiagram R A)

def subgroupTotalCochains : CochainComplex (ModuleCat.{u} R) ℕ :=
  cochainReplacementTotal (L.subgroupCochainDiagram R A)

theorem subgroupBicomplex_term (i n : ℕ) :
    ((L.subgroupBicomplex R A).X i).X n =
      ModuleCat.of R (∀ s : ComposableArrows F.CentricOrbit i,
        ((SingularCohomology.chainsFunctor R).obj
          (L.subgroupDiagram.obj (chainHead s))).X n ⟶ A) := rfl

theorem subgroupBicomplex_vertical (i n : ℕ)
    (x : ((L.subgroupBicomplex R A).X i).X n)
    (s : ComposableArrows F.CentricOrbit i) :
    ((L.subgroupBicomplex R A).X i).d n (n+1) x s =
      (((SingularCohomology.chainsFunctor R).obj
          (L.subgroupDiagram.obj (chainHead s))).d (n+1) n) ≫ x s :=
  cochainReplacementBicomplex_vertical (L.subgroupCochainDiagram R A) i n x s

def subgroupCochainCoefficientMap {B : ModuleCat.{u} R} (a : A ⟶ B) :
    L.subgroupCochainDiagram R A ⟶ L.subgroupCochainDiagram R B :=
  Functor.whiskerLeft L.subgroupDiagram.op (SingularCohomology.coefficientNatTrans R a)

theorem subgroupCochainCoefficientMap_component {B : ModuleCat.{u} R} (a : A ⟶ B)
    (P : F.CentricOrbit) (n : ℕ)
    (z : ((SingularCohomology.chainsFunctor R).obj (L.subgroupDiagram.obj P)).X n ⟶ A) :
    ((L.subgroupCochainCoefficientMap R A a).app (op P)).f n z = z ≫ a := rfl

end Sharpness.FusionSystem.CentricLinkingSystem
