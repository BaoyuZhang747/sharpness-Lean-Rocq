import Sharpness.TotalDualCochainIso
import Sharpness.NormalizerTotalDualComponents

/-! The actual normalizer total cochain complex is the Hom dual of the
actual normalizer total chain complex, with arbitrary coefficients.
The comparison commutes with the full differential, retains every
previously fixed string component, and induces native cohomology
isomorphisms. No geometric comparison is asserted here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory Simplicial
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

def normalizerTotalDualCochainIso :
    I.normalizerTotalCochains R A ≅ ChainComplex.linearYonedaObj (I.normalizerTotalChains R) R A :=
  (I.normalizerDualBicomplexTotalIso R A).symm ≪≫
    (totalDualCochainIso (I.normalizerChainBicomplex R) A).symm

theorem normalizerTotalDualCochainIso_hom_f (n : ℕ) :
    (I.normalizerTotalDualCochainIso R A).hom.f n = (I.normalizerTotalDualDegreeIso R A n).hom := rfl

theorem normalizerTotalDualCochainIso_inv_f (n : ℕ) :
    (I.normalizerTotalDualCochainIso R A).inv.f n = (I.normalizerTotalDualDegreeIso R A n).inv := rfl

theorem normalizerTotalDualCochainIso_component (p q n : ℕ) (h : p+q=n)
    (s : ComposableArrows F.NormalizerCategory p) (f : (I.normalizerTotalChains R).X n ⟶ A) :
    totalSummandProjectionAt (I.normalizerBicomplex R A) p q n h
        ((I.normalizerTotalDualCochainIso R A).inv.f n f) s =
      ((chainReplacementInclusion (I.normalizerChainDiagram R) ⦋p⦌ s).f q ≫
        (I.normalizerChainBicomplex R).ιTotal (ComplexShape.down ℕ) p q n h) ≫ f :=
  I.normalizerTotalDualDegreeIso_component R A p q n h s f

def normalizerTotalDualCohomologyIso (n : ℕ) :
    (I.normalizerTotalCochains R A).homology n ≅
      (ChainComplex.linearYonedaObj (I.normalizerTotalChains R) R A).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).mapIso
    (I.normalizerTotalDualCochainIso R A)

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
