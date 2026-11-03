import Sharpness.LinkingSubgroupCochains
import Sharpness.CategoryCochainReplacementFunctor

/-! Coefficient homomorphisms act on the actual double cochain and total
complexes by postcomposition. Both differential compatibilities are
inherited from the constructed replacement functor. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R]
    {A B : ModuleCat.{u} R} (a : A ⟶ B)

def subgroupBicomplexCoefficientMap : L.subgroupBicomplex R A ⟶ L.subgroupBicomplex R B :=
  cochainReplacementBicomplexFunctor.map (L.subgroupCochainCoefficientMap R A a)

def subgroupTotalCoefficientMap :
    L.subgroupTotalCochains R A ⟶ L.subgroupTotalCochains R B :=
  cochainReplacementTotalFunctor.map (L.subgroupCochainCoefficientMap R A a)

theorem subgroupBicomplexCoefficientMap_component (i n : ℕ)
    (x : ((L.subgroupBicomplex R A).X i).X n)
    (s : ComposableArrows F.CentricOrbit i) :
    ((L.subgroupBicomplexCoefficientMap R a).f i).f n x s = x s ≫ a := rfl

theorem subgroupBicomplexCoefficientMap_id :
    L.subgroupBicomplexCoefficientMap R (𝟙 A) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  change x s ≫ 𝟙 A = x s
  exact Category.comp_id _

theorem subgroupBicomplexCoefficientMap_comp {C : ModuleCat.{u} R} (b : B ⟶ C) :
    L.subgroupBicomplexCoefficientMap R (a ≫ b) =
      L.subgroupBicomplexCoefficientMap R a ≫ L.subgroupBicomplexCoefficientMap R b := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  change x s ≫ (a ≫ b) = (x s ≫ a) ≫ b
  exact (Category.assoc _ _ _).symm

end Sharpness.FusionSystem.CentricLinkingSystem
