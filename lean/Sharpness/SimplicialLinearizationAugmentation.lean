import Sharpness.SimplicialReplacementLinearizationNaturality
import Sharpness.SimplicialReplacementAugmentation

/-! Column linearization preserves the actual cocone augmentation.
The equality is of entire chain maps and is checked on every actual
simplicial summand, before any geometric quasi-isomorphism is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C : Type u} [Category.{u} C] (D : C ⥤ SSet.{u})
    (R : Type u) [CommRing R] {X : SSet.{u}}
    (a : D ⟶ (Functor.const C).obj X)

theorem simplicialReplacementInclusion_augmentation (i : SimplexCategory)
    (s : ComposableArrows C i.len) :
    simplicialReplacementInclusion D i s ≫ simplicialReplacementColumnAugmentation D a i =
      a.app (chainHead s) := rfl

def simplicialChainCoconeColumn (i : SimplexCategory) :
    chainReplacementColumn (simplicialChainDiagram D R) i ⟶
      X.chainComplex (ModuleCat.of R R) :=
  coproductChainsDesc _ (fun s => (simplicialChainsFunctor R).map (a.app (chainHead s)))

theorem simplicialColumnLinearization_augmentation (i : SimplexCategory) :
    (simplicialColumnLinearizationIso D R i).hom ≫
        (simplicialChainsFunctor R).map (simplicialReplacementColumnAugmentation D a i) =
      simplicialChainCoconeColumn D R a i := by
  rw [simplicialColumnLinearizationIso_hom]
  apply coproductChains_hom_ext
  intro s
  change chainReplacementInclusion (simplicialChainDiagram D R) i s ≫
      (simplicialColumnLinearizationHom D R i ≫
        (simplicialChainsFunctor R).map (simplicialReplacementColumnAugmentation D a i)) =
    chainReplacementInclusion (simplicialChainDiagram D R) i s ≫ simplicialChainCoconeColumn D R a i
  calc
    _ = (simplicialChainsFunctor R).map (simplicialReplacementInclusion D i s) ≫
        (simplicialChainsFunctor R).map (simplicialReplacementColumnAugmentation D a i) := by
      rw [← Category.assoc, simplicialColumnLinearizationHom_inclusion]
    _ = (simplicialChainsFunctor R).map
        (simplicialReplacementInclusion D i s ≫ simplicialReplacementColumnAugmentation D a i) :=
      ((simplicialChainsFunctor R).map_comp _ _).symm
    _ = (simplicialChainsFunctor R).map (a.app (chainHead s)) :=
      congrArg (fun t => (simplicialChainsFunctor R).map t)
        (simplicialReplacementInclusion_augmentation D a i s)
    _ = _ := (coproductChainsInclusion_desc
      (fun t : ComposableArrows C i.len => (simplicialChainDiagram D R).obj (chainHead t))
      (fun t => (simplicialChainsFunctor R).map (a.app (chainHead t))) s).symm

theorem simplicialChainCoconeColumn_naturality {i j : SimplexCategory} (f : i ⟶ j) :
    chainReplacementMap (simplicialChainDiagram D R) f ≫ simplicialChainCoconeColumn D R a i =
      simplicialChainCoconeColumn D R a j := by
  rw [← simplicialColumnLinearization_augmentation, ← simplicialColumnLinearization_augmentation,
    ← Category.assoc, simplicialColumnLinearization_naturality, Category.assoc,
    ← (simplicialChainsFunctor R).map_comp,
    simplicialReplacementColumnAugmentation_naturality]

end Sharpness
