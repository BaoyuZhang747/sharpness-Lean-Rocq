import Sharpness.NormalizerTotalDualDegree
import Sharpness.TotalDualProjection
import Sharpness.TotalProjectionNaturality

/-! The inverse of the actual normalizer total-degree comparison is
fixed at every string: its value is precomposition with the actual
string-chain inclusion followed by the actual total-chain inclusion. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory Simplicial
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
theorem normalizerTotalDualDegreeIso_component (p q n : ℕ) (h : p+q=n)
    (s : ComposableArrows F.NormalizerCategory p) (f : (I.normalizerTotalChains R).X n ⟶ A) :
    totalSummandProjectionAt (I.normalizerBicomplex R A) p q n h
        ((I.normalizerTotalDualDegreeIso R A n).inv f) s =
      ((chainReplacementInclusion (I.normalizerChainDiagram R) ⦋p⦌ s).f q ≫
        (I.normalizerChainBicomplex R).ιTotal (ComplexShape.down ℕ) p q n h) ≫ f := by
  let K := I.normalizerChainBicomplex R
  let a := (totalDualDegreeIso K A n).inv f
  have hn := totalMap_projection (dualNatBicomplex K A) (I.normalizerBicomplex R A)
    (I.normalizerBicomplexDualIso R A).hom p q n h
  have hs := congrArg (fun b => b a s) hn
  calc
    _ = (chainReplacementInclusion (I.normalizerChainDiagram R) ⦋p⦌ s).f q ≫
        totalSummandProjectionAt (dualNatBicomplex K A) p q n h a := hs
    _ = (chainReplacementInclusion (I.normalizerChainDiagram R) ⦋p⦌ s).f q ≫
        (K.ιTotal (ComplexShape.down ℕ) p q n h ≫ f) :=
      congrArg (fun b => (chainReplacementInclusion (I.normalizerChainDiagram R) ⦋p⦌ s).f q ≫ b)
        (totalDualDegreeIso_inv_totalProjection K A n ⟨(p,q),h⟩ f)
    _ = _ := (Category.assoc _ _ _).symm

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
