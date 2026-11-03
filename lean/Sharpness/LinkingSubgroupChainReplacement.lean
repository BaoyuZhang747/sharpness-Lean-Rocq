import Sharpness.LinkingSubgroupCochains
import Sharpness.CategoryChainReplacementDual
import Sharpness.CategoryChainReplacementTotal

/-! The actual covariant singular-chain diagram of the subgroup
spaces and its simplicial direct-sum replacement. Dualization is
identified with the manuscript's already constructed cosimplicial
cochain replacement, for every coefficient module. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R]

def subgroupChainDiagram : F.CentricOrbit ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  L.subgroupDiagram ⋙ SingularCohomology.chainsFunctor R

def subgroupChainReplacement : SimplicialObject (ChainComplex (ModuleCat.{u} R) ℕ) :=
  chainReplacement (L.subgroupChainDiagram R)

def subgroupChainBicomplex :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  chainReplacementBicomplex (L.subgroupChainDiagram R)

def subgroupTotalChains : ChainComplex (ModuleCat.{u} R) ℕ :=
  chainReplacementTotal (L.subgroupChainDiagram R)

theorem subgroupChainBicomplex_term (i n : ℕ) :
    ((L.subgroupChainBicomplex R).X i).X n =
      moduleDirectSum (fun s : ComposableArrows F.CentricOrbit i =>
        ((SingularCohomology.chainsFunctor R).obj (L.subgroupDiagram.obj (chainHead s))).X n) := rfl

set_option backward.isDefEq.respectTransparency false in
def subgroupChainReplacementDualIso (A : ModuleCat.{u} R) :
    (L.subgroupChainReplacement R).rightOp ⋙ SingularCohomology.chainDualFunctor R A ≅
      cochainReplacement (L.subgroupCochainDiagram R A) :=
  chainReplacementDualIso (L.subgroupChainDiagram R) A

theorem subgroupChainReplacementDualIso_component (A : ModuleCat.{u} R) (i : SimplexCategory)
    (n : ℕ) (f : (chainReplacementColumn (L.subgroupChainDiagram R) i).X n ⟶ A)
    (s : ComposableArrows F.CentricOrbit i.len) :
    (((L.subgroupChainReplacementDualIso R A).app i).hom.f n) f s =
      (chainReplacementInclusion (L.subgroupChainDiagram R) i s).f n ≫ f := rfl

end Sharpness.FusionSystem.CentricLinkingSystem
