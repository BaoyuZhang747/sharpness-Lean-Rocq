import Sharpness.NormalizerAlexanderWhitney
import Sharpness.ReplacementAlexanderWhitneyFaces
import Sharpness.ChainTotalProjectionNaturality

/-! The actual normalizer Alexander–Whitney comparison has the
required zero-column formula after the proved inverse linearization:
each diagonal generator retains its actual head normalizer simplex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat) (R : Type u) [CommRing R]
    (ez : EilenbergZilberInput.{u} R)

theorem normalizerSingularInverseLinearization_projection (n : ℕ) (h : 0+n=n) :
    (I.normalizerSingularTotalLinearizationIso R).inv.f n ≫
        chainTotalProjection (I.normalizerChainBicomplex R) 0 n n h =
      chainTotalProjection (I.normalizerSingularLinearizedBicomplex R) 0 n n h ≫
        ((I.normalizerSingularBicomplexLinearizationIso R).inv.f 0).f n :=
  chainTotalMap_projection (I.normalizerSingularLinearizedBicomplex R) (I.normalizerChainBicomplex R)
    (I.normalizerSingularBicomplexLinearizationIso R).inv 0 n n h

theorem normalizerAlexanderWhitney_zeroColumn (n : ℕ) (h : 0+n=n)
    (s : ComposableArrows F.NormalizerCategory n)
    (x : (I.normalizerSingularDiagram.obj (chainHead s)).obj (op ⦋n⦌)) :
    I.normalizerSingularDiagonal.ιChainComplex (R := ModuleCat.of R R) ⟨s, x⟩ ≫
        (I.normalizerAlexanderWhitney R ez).f n ≫
        chainTotalProjection (I.normalizerChainBicomplex R) 0 n n h =
      (I.normalizerSingularDiagram.obj (chainHead s)).ιChainComplex x ≫
        (chainReplacementInclusion (I.normalizerChainDiagram R) ⦋0⦌
          (ComposableArrows.mk₀ (chainHead s))).f n := by
  change I.normalizerSingularDiagonal.ιChainComplex ⟨s, x⟩ ≫
      ((ez.alexanderWhitney I.normalizerSingularReplacement).f n ≫
        (I.normalizerSingularTotalLinearizationIso R).inv.f n) ≫
      chainTotalProjection (I.normalizerChainBicomplex R) 0 n n h = _
  rw [Category.assoc, normalizerSingularInverseLinearization_projection, ← Category.assoc]
  calc
    _ = (simplicialReplacementColumn I.normalizerSingularDiagram ⦋0⦌).ιChainComplex
        (replacementSimplex I.normalizerSingularDiagram ⦋0⦌ (op ⦋n⦌)
          (ComposableArrows.mk₀ (chainHead s)) x) ≫
        ((I.normalizerSingularBicomplexLinearizationIso R).inv.f 0).f n :=
      congrArg (fun t => t ≫ ((I.normalizerSingularBicomplexLinearizationIso R).inv.f 0).f n)
        (replacementAlexanderWhitney_zeroColumn I.normalizerSingularDiagram ez n h s x)
    _ = _ := simplicialColumnLinearizationInvDegree_simplex I.normalizerSingularDiagram R ⦋0⦌ n
      (ComposableArrows.mk₀ (chainHead s)) x

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
