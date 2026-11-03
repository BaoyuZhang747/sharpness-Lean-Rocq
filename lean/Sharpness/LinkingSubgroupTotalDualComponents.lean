import Sharpness.LinkingSubgroupTotalDualDegree
import Sharpness.TotalDualProjection
import Sharpness.TotalProjectionNaturality

/-! The inverse of the actual subgroup total-degree comparison is
fixed at every string: its value is precomposition with the actual
string-chain inclusion followed by the actual total-chain inclusion. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Simplicial
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
theorem subgroupTotalDualDegreeIso_component (p q n : ℕ) (h : p+q=n)
    (s : ComposableArrows F.CentricOrbit p) (f : (L.subgroupTotalChains R).X n ⟶ A) :
    totalSummandProjectionAt (L.subgroupBicomplex R A) p q n h
        ((L.subgroupTotalDualDegreeIso R A n).inv f) s =
      ((chainReplacementInclusion (L.subgroupChainDiagram R) ⦋p⦌ s).f q ≫
        (L.subgroupChainBicomplex R).ιTotal (ComplexShape.down ℕ) p q n h) ≫ f := by
  let K := L.subgroupChainBicomplex R
  let a := (totalDualDegreeIso K A n).inv f
  have hn := totalMap_projection (dualNatBicomplex K A) (L.subgroupBicomplex R A)
    (L.subgroupBicomplexDualIso R A).hom p q n h
  have hs := congrArg (fun b => b a s) hn
  calc
    _ = (chainReplacementInclusion (L.subgroupChainDiagram R) ⦋p⦌ s).f q ≫
        totalSummandProjectionAt (dualNatBicomplex K A) p q n h a := hs
    _ = (chainReplacementInclusion (L.subgroupChainDiagram R) ⦋p⦌ s).f q ≫
        (K.ιTotal (ComplexShape.down ℕ) p q n h ≫ f) :=
      congrArg (fun b => (chainReplacementInclusion (L.subgroupChainDiagram R) ⦋p⦌ s).f q ≫ b)
        (totalDualDegreeIso_inv_totalProjection K A n ⟨(p,q),h⟩ f)
    _ = _ := (Category.assoc _ _ _).symm

end Sharpness.FusionSystem.CentricLinkingSystem
