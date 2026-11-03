import Sharpness.SimplicialReplacementLinearizationNaturality
import Sharpness.LinkingSubgroupSingularReplacement
import Sharpness.LinkingSubgroupChainReplacement
import Sharpness.SimplicialLinearizationAugmentation
import Sharpness.LinkingSubgroupSingularAugmentation

/-! The actual subgroup chain replacement is the linearization of
the actual bisimplicial singular replacement, as a simplicial object,
as an entire bicomplex, and as its signed native total complex. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R]

def subgroupSingularLinearizationIso :
    L.subgroupChainReplacement R ≅ L.subgroupSingularReplacement ⋙ simplicialChainsFunctor R :=
  simplicialReplacementLinearizationIso L.subgroupSingularDiagram R

def subgroupSingularLinearizedBicomplex :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  simplicialReplacementLinearizedBicomplex L.subgroupSingularDiagram R

def subgroupSingularBicomplexLinearizationIso :
    L.subgroupChainBicomplex R ≅ L.subgroupSingularLinearizedBicomplex R :=
  simplicialReplacementBicomplexLinearizationIso L.subgroupSingularDiagram R

def subgroupSingularLinearizedTotal : ChainComplex (ModuleCat.{u} R) ℕ :=
  simplicialReplacementLinearizedTotal L.subgroupSingularDiagram R

def subgroupSingularTotalLinearizationIso :
    L.subgroupTotalChains R ≅ L.subgroupSingularLinearizedTotal R :=
  simplicialReplacementTotalLinearizationIso L.subgroupSingularDiagram R

theorem subgroupSingularLinearizationIso_simplex (i : SimplexCategory) (n : ℕ)
    (s : ComposableArrows F.CentricOrbit i.len)
    (x : (L.subgroupSingularDiagram.obj (chainHead s)).obj (op ⦋n⦌)) :
    (L.subgroupSingularDiagram.obj (chainHead s)).ιChainComplex (R := ModuleCat.of R R) x ≫
        (chainReplacementInclusion (L.subgroupChainDiagram R) i s).f n ≫
        ((L.subgroupSingularLinearizationIso R).app (op i)).hom.f n =
      (simplicialReplacementColumn L.subgroupSingularDiagram i).ιChainComplex ⟨s, x⟩ :=
  simplicialColumnLinearizationHom_simplex L.subgroupSingularDiagram R i n s x

theorem subgroupSingularLinearizationIso_augmentation (i : SimplexCategory) :
    ((L.subgroupSingularLinearizationIso R).app (op i)).hom ≫
        SSet.chainComplexMap
          (simplicialReplacementColumnAugmentation L.subgroupSingularDiagram L.subgroupSingularCocone i)
          (ModuleCat.of R R) =
      coproductChainsDesc
        (fun s : ComposableArrows F.CentricOrbit i.len => (L.subgroupChainDiagram R).obj (chainHead s))
        (fun s => (SingularCohomology.chainsFunctor R).map (L.subgroupDiagramForget (chainHead s))) :=
  simplicialColumnLinearization_augmentation L.subgroupSingularDiagram R L.subgroupSingularCocone i

end Sharpness.FusionSystem.CentricLinkingSystem
