import Sharpness.LibmanNormalizerMaps
import Sharpness.SingularCochainFunctor
import Sharpness.CategoryCochainReplacementLaws

/-! The actual K^n of the manuscript, defined by pullback in the fixed
realized Libman diagram. This also constructs its literal replacement
bicomplex and total cochains, with every string and differential retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerData
open CategoryTheory Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} (D : L.LibmanNormalizerData)
    (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

def cochainDiagram : F.NormalizerCategoryᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  D.diagram.op ⋙ SingularCohomology.cochainFunctor R A

def cohomologyDiagram (n : ℕ) : F.NormalizerCategoryᵒᵖ ⥤ ModuleCat.{u} R :=
  D.cochainDiagram R A ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n

theorem cohomologyDiagram_obj (d : F.NormalizerCategory) (n : ℕ) :
    (D.cohomologyDiagram R A n).obj (op d) =
      SingularCohomology.cohomology R (D.diagram.obj d) A n := rfl

theorem cohomologyDiagram_map {d e : F.NormalizerCategory} (a : d ⟶ e) (n : ℕ) :
    (D.cohomologyDiagram R A n).map a.op =
      SingularCohomology.pull R (D.diagram.map a) A n := rfl

def bicomplex : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  cochainReplacementBicomplex (D.cochainDiagram R A)

def totalCochains : CochainComplex (ModuleCat.{u} R) ℕ :=
  cochainReplacementTotal (D.cochainDiagram R A)

theorem bicomplex_term (i n : ℕ) :
    ((D.bicomplex R A).X i).X n =
      ModuleCat.of R (∀ s : ComposableArrows F.NormalizerCategory i,
        ((SingularCohomology.chainsFunctor R).obj (D.diagram.obj (chainHead s))).X n ⟶ A) := rfl

theorem bicomplex_vertical (i n : ℕ) (x : ((D.bicomplex R A).X i).X n)
    (s : ComposableArrows F.NormalizerCategory i) :
    ((D.bicomplex R A).X i).d n (n+1) x s =
      (((SingularCohomology.chainsFunctor R).obj (D.diagram.obj (chainHead s))).d (n+1) n) ≫ x s :=
  cochainReplacementBicomplex_vertical (D.cochainDiagram R A) i n x s

def cochainCoefficientMap {B : ModuleCat.{u} R} (a : A ⟶ B) :
    D.cochainDiagram R A ⟶ D.cochainDiagram R B :=
  Functor.whiskerLeft D.diagram.op (SingularCohomology.coefficientNatTrans R a)

theorem cochainCoefficientMap_component {B : ModuleCat.{u} R} (a : A ⟶ B)
    (d : F.NormalizerCategory) (n : ℕ)
    (z : ((SingularCohomology.chainsFunctor R).obj (D.diagram.obj d)).X n ⟶ A) :
    ((D.cochainCoefficientMap R A a).app (op d)).f n z = z ≫ a := rfl

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerData
