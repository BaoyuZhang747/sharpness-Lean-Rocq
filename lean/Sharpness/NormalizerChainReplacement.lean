import Sharpness.NormalizerGeometryBase
import Sharpness.CategoryChainReplacementDual
import Sharpness.CategoryChainReplacementTotal

/-! The actual covariant singular-chain diagram of the normalizer
spaces and its simplicial direct-sum replacement. Dualization is
identified with the manuscript's already constructed cosimplicial
cochain replacement, for every coefficient module. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat) (R : Type u) [CommRing R]

def normalizerChainDiagram : F.NormalizerCategory ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  I.normalizerDiagram ⋙ SingularCohomology.chainsFunctor R

def normalizerChainReplacement : SimplicialObject (ChainComplex (ModuleCat.{u} R) ℕ) :=
  chainReplacement (I.normalizerChainDiagram R)

def normalizerChainBicomplex :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  chainReplacementBicomplex (I.normalizerChainDiagram R)

def normalizerTotalChains : ChainComplex (ModuleCat.{u} R) ℕ :=
  chainReplacementTotal (I.normalizerChainDiagram R)

theorem normalizerChainBicomplex_term (i n : ℕ) :
    ((I.normalizerChainBicomplex R).X i).X n =
      moduleDirectSum (fun s : ComposableArrows F.NormalizerCategory i =>
        ((SingularCohomology.chainsFunctor R).obj (I.normalizerDiagram.obj (chainHead s))).X n) := rfl

set_option backward.isDefEq.respectTransparency false in
def normalizerChainReplacementDualIso (A : ModuleCat.{u} R) :
    (I.normalizerChainReplacement R).rightOp ⋙ SingularCohomology.chainDualFunctor R A ≅
      cochainReplacement (I.normalizerCochainDiagram R A) :=
  chainReplacementDualIso (I.normalizerChainDiagram R) A

theorem normalizerChainReplacementDualIso_component (A : ModuleCat.{u} R) (i : SimplexCategory)
    (n : ℕ) (f : (chainReplacementColumn (I.normalizerChainDiagram R) i).X n ⟶ A)
    (s : ComposableArrows F.NormalizerCategory i.len) :
    (((I.normalizerChainReplacementDualIso R A).app i).hom.f n) f s =
      (chainReplacementInclusion (I.normalizerChainDiagram R) i s).f n ≫ f := rfl

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
