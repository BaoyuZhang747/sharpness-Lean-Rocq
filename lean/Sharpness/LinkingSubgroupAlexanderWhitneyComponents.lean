import Sharpness.LinkingSubgroupAlexanderWhitney
import Sharpness.ReplacementAlexanderWhitneyFaces
import Sharpness.ChainTotalProjectionNaturality

/-! The actual subgroup Alexander–Whitney comparison has the
required zero-column formula after the proved inverse linearization:
each diagonal generator retains its actual head subgroup simplex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R]
    (ez : EilenbergZilberInput.{u} R)

theorem subgroupSingularInverseLinearization_projection (n : ℕ) (h : 0+n=n) :
    (L.subgroupSingularTotalLinearizationIso R).inv.f n ≫
        chainTotalProjection (L.subgroupChainBicomplex R) 0 n n h =
      chainTotalProjection (L.subgroupSingularLinearizedBicomplex R) 0 n n h ≫
        ((L.subgroupSingularBicomplexLinearizationIso R).inv.f 0).f n :=
  chainTotalMap_projection (L.subgroupSingularLinearizedBicomplex R) (L.subgroupChainBicomplex R)
    (L.subgroupSingularBicomplexLinearizationIso R).inv 0 n n h

theorem subgroupAlexanderWhitney_zeroColumn (n : ℕ) (h : 0+n=n)
    (s : ComposableArrows F.CentricOrbit n)
    (x : (L.subgroupSingularDiagram.obj (chainHead s)).obj (op ⦋n⦌)) :
    L.subgroupSingularDiagonal.ιChainComplex (R := ModuleCat.of R R) ⟨s, x⟩ ≫
        (L.subgroupAlexanderWhitney R ez).f n ≫
        chainTotalProjection (L.subgroupChainBicomplex R) 0 n n h =
      (L.subgroupSingularDiagram.obj (chainHead s)).ιChainComplex x ≫
        (chainReplacementInclusion (L.subgroupChainDiagram R) ⦋0⦌
          (ComposableArrows.mk₀ (chainHead s))).f n := by
  change L.subgroupSingularDiagonal.ιChainComplex ⟨s, x⟩ ≫
      ((ez.alexanderWhitney L.subgroupSingularReplacement).f n ≫
        (L.subgroupSingularTotalLinearizationIso R).inv.f n) ≫
      chainTotalProjection (L.subgroupChainBicomplex R) 0 n n h = _
  rw [Category.assoc, subgroupSingularInverseLinearization_projection, ← Category.assoc]
  calc
    _ = (simplicialReplacementColumn L.subgroupSingularDiagram ⦋0⦌).ιChainComplex
        (replacementSimplex L.subgroupSingularDiagram ⦋0⦌ (op ⦋n⦌)
          (ComposableArrows.mk₀ (chainHead s)) x) ≫
        ((L.subgroupSingularBicomplexLinearizationIso R).inv.f 0).f n :=
      congrArg (fun t => t ≫ ((L.subgroupSingularBicomplexLinearizationIso R).inv.f 0).f n)
        (replacementAlexanderWhitney_zeroColumn L.subgroupSingularDiagram ez n h s x)
    _ = _ := simplicialColumnLinearizationInvDegree_simplex L.subgroupSingularDiagram R ⦋0⦌ n
      (ComposableArrows.mk₀ (chainHead s)) x

end Sharpness.FusionSystem.CentricLinkingSystem
