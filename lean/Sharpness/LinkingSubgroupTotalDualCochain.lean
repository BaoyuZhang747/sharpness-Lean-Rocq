import Sharpness.TotalDualCochainIso
import Sharpness.LinkingSubgroupTotalDualComponents

/-! The actual subgroup total cochain complex is the Hom dual of the
actual subgroup total chain complex, with arbitrary coefficients.
The comparison commutes with the full differential, retains every
previously fixed string component, and induces native cohomology
isomorphisms. No geometric comparison is asserted here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Simplicial
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

def subgroupTotalDualCochainIso :
    L.subgroupTotalCochains R A ≅ ChainComplex.linearYonedaObj (L.subgroupTotalChains R) R A :=
  (L.subgroupDualBicomplexTotalIso R A).symm ≪≫
    (totalDualCochainIso (L.subgroupChainBicomplex R) A).symm

theorem subgroupTotalDualCochainIso_hom_f (n : ℕ) :
    (L.subgroupTotalDualCochainIso R A).hom.f n = (L.subgroupTotalDualDegreeIso R A n).hom := rfl

theorem subgroupTotalDualCochainIso_inv_f (n : ℕ) :
    (L.subgroupTotalDualCochainIso R A).inv.f n = (L.subgroupTotalDualDegreeIso R A n).inv := rfl

theorem subgroupTotalDualCochainIso_component (p q n : ℕ) (h : p+q=n)
    (s : ComposableArrows F.CentricOrbit p) (f : (L.subgroupTotalChains R).X n ⟶ A) :
    totalSummandProjectionAt (L.subgroupBicomplex R A) p q n h
        ((L.subgroupTotalDualCochainIso R A).inv.f n f) s =
      ((chainReplacementInclusion (L.subgroupChainDiagram R) ⦋p⦌ s).f q ≫
        (L.subgroupChainBicomplex R).ιTotal (ComplexShape.down ℕ) p q n h) ≫ f :=
  L.subgroupTotalDualDegreeIso_component R A p q n h s f

def subgroupTotalDualCohomologyIso (n : ℕ) :
    (L.subgroupTotalCochains R A).homology n ≅
      (ChainComplex.linearYonedaObj (L.subgroupTotalChains R) R A).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).mapIso
    (L.subgroupTotalDualCochainIso R A)

end Sharpness.FusionSystem.CentricLinkingSystem
