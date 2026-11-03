import Sharpness.SimplicialReplacementLinearizationNaturality
import Sharpness.NormalizerSingularReplacement
import Sharpness.NormalizerChainReplacement
import Sharpness.SimplicialLinearizationAugmentation
import Sharpness.NormalizerSingularAugmentation

/-! The actual normalizer chain replacement is the linearization of
the actual bisimplicial singular replacement, as a simplicial object,
as an entire bicomplex, and as its signed native total complex. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat) (R : Type u) [CommRing R]

def normalizerSingularLinearizationIso :
    I.normalizerChainReplacement R ≅ I.normalizerSingularReplacement ⋙ simplicialChainsFunctor R :=
  simplicialReplacementLinearizationIso I.normalizerSingularDiagram R

def normalizerSingularLinearizedBicomplex :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  simplicialReplacementLinearizedBicomplex I.normalizerSingularDiagram R

def normalizerSingularBicomplexLinearizationIso :
    I.normalizerChainBicomplex R ≅ I.normalizerSingularLinearizedBicomplex R :=
  simplicialReplacementBicomplexLinearizationIso I.normalizerSingularDiagram R

def normalizerSingularLinearizedTotal : ChainComplex (ModuleCat.{u} R) ℕ :=
  simplicialReplacementLinearizedTotal I.normalizerSingularDiagram R

def normalizerSingularTotalLinearizationIso :
    I.normalizerTotalChains R ≅ I.normalizerSingularLinearizedTotal R :=
  simplicialReplacementTotalLinearizationIso I.normalizerSingularDiagram R

theorem normalizerSingularLinearizationIso_simplex (i : SimplexCategory) (n : ℕ)
    (s : ComposableArrows F.NormalizerCategory i.len)
    (x : (I.normalizerSingularDiagram.obj (chainHead s)).obj (op ⦋n⦌)) :
    (I.normalizerSingularDiagram.obj (chainHead s)).ιChainComplex (R := ModuleCat.of R R) x ≫
        (chainReplacementInclusion (I.normalizerChainDiagram R) i s).f n ≫
        ((I.normalizerSingularLinearizationIso R).app (op i)).hom.f n =
      (simplicialReplacementColumn I.normalizerSingularDiagram i).ιChainComplex ⟨s, x⟩ :=
  simplicialColumnLinearizationHom_simplex I.normalizerSingularDiagram R i n s x

theorem normalizerSingularLinearizationIso_augmentation (i : SimplexCategory) :
    ((I.normalizerSingularLinearizationIso R).app (op i)).hom ≫
        SSet.chainComplexMap
          (simplicialReplacementColumnAugmentation I.normalizerSingularDiagram I.normalizerSingularCocone i)
          (ModuleCat.of R R) =
      coproductChainsDesc
        (fun s : ComposableArrows F.NormalizerCategory i.len => (I.normalizerChainDiagram R).obj (chainHead s))
        (fun s => (SingularCohomology.chainsFunctor R).map (I.normalizerDiagramForget (chainHead s))) :=
  simplicialColumnLinearization_augmentation I.normalizerSingularDiagram R I.normalizerSingularCocone i

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
