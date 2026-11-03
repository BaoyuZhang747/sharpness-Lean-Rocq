import Sharpness.LinkingSubgroupTotalDualCochain

/-! Evaluation of the forward actual total-dual isomorphism on
every string inclusion. This follows from the proved inverse formula
and its actual inverse identity, without any geometric input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Simplicial
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

theorem subgroupTotalDualCochainIso_evaluation (p q n : ℕ) (h : p+q=n)
    (s : ComposableArrows F.CentricOrbit p) (v : (L.subgroupTotalCochains R A).X n) :
    ((chainReplacementInclusion (L.subgroupChainDiagram R) ⦋p⦌ s).f q ≫
        (L.subgroupChainBicomplex R).ιTotal (ComplexShape.down ℕ) p q n h) ≫
        ((L.subgroupTotalDualCochainIso R A).hom.f n v) =
      totalSummandProjectionAt (L.subgroupBicomplex R A) p q n h v s := by
  let e := L.subgroupTotalDualCochainIso R A
  have hv : e.inv.f n (e.hom.f n v) = v :=
    congrArg (fun t => t v) (HomologicalComplex.congr_hom e.hom_inv_id n)
  exact (L.subgroupTotalDualCochainIso_component R A p q n h s (e.hom.f n v)).symm.trans
    (congrArg (fun t => totalSummandProjectionAt (L.subgroupBicomplex R A) p q n h t s) hv)

end Sharpness.FusionSystem.CentricLinkingSystem
