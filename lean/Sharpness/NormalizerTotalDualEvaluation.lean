import Sharpness.NormalizerTotalDualCochain

/-! Evaluation of the forward actual total-dual isomorphism on
every string inclusion. This follows from the proved inverse formula
and its actual inverse identity, without any geometric input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory Simplicial
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

theorem normalizerTotalDualCochainIso_evaluation (p q n : ℕ) (h : p+q=n)
    (s : ComposableArrows F.NormalizerCategory p) (v : (I.normalizerTotalCochains R A).X n) :
    ((chainReplacementInclusion (I.normalizerChainDiagram R) ⦋p⦌ s).f q ≫
        (I.normalizerChainBicomplex R).ιTotal (ComplexShape.down ℕ) p q n h) ≫
        ((I.normalizerTotalDualCochainIso R A).hom.f n v) =
      totalSummandProjectionAt (I.normalizerBicomplex R A) p q n h v s := by
  let e := I.normalizerTotalDualCochainIso R A
  have hv : e.inv.f n (e.hom.f n v) = v :=
    congrArg (fun t => t v) (HomologicalComplex.congr_hom e.hom_inv_id n)
  exact (I.normalizerTotalDualCochainIso_component R A p q n h s (e.hom.f n v)).symm.trans
    (congrArg (fun t => totalSummandProjectionAt (I.normalizerBicomplex R A) p q n h t s) hv)

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
