import Sharpness.SimplicialReplacementLinearization
import Sharpness.CategoryChainReplacementTotal

/-! The explicit column linearization is natural in all horizontal
simplex maps. It therefore identifies the entire simplicial chain
replacement, its alternating-face bicomplex, and its signed total. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C : Type u} [Category.{u} C] (D : C ⥤ SSet.{u})
    (R : Type u) [CommRing R]

theorem simplicialColumnLinearization_naturality {i j : SimplexCategory} (f : i ⟶ j) :
    chainReplacementMap (simplicialChainDiagram D R) f ≫
        (simplicialColumnLinearizationIso D R i).hom =
      (simplicialColumnLinearizationIso D R j).hom ≫
        SSet.chainComplexMap (simplicialReplacementMap D f) (ModuleCat.of R R) := by
  rw [simplicialColumnLinearizationIso_hom, simplicialColumnLinearizationIso_hom]
  apply coproductChains_hom_ext
  intro s
  change chainReplacementInclusion (simplicialChainDiagram D R) j s ≫
      (chainReplacementMap (simplicialChainDiagram D R) f ≫
        simplicialColumnLinearizationHom D R i) =
    chainReplacementInclusion (simplicialChainDiagram D R) j s ≫
      (simplicialColumnLinearizationHom D R j ≫
        SSet.chainComplexMap (simplicialReplacementMap D f) (ModuleCat.of R R))
  calc
    _ = (simplicialChainDiagram D R).map (categoryChainHeadArrow f s) ≫
        (chainReplacementInclusion (simplicialChainDiagram D R) i (restrictCategoryChain f s) ≫
          simplicialColumnLinearizationHom D R i) := by
      rw [← Category.assoc, chainReplacementMap_inclusion, Category.assoc]
    _ = (simplicialChainsFunctor R).map (D.map (categoryChainHeadArrow f s)) ≫
        (simplicialChainsFunctor R).map
          (simplicialReplacementInclusion D i (restrictCategoryChain f s)) :=
      congrArg (fun t => (simplicialChainDiagram D R).map (categoryChainHeadArrow f s) ≫ t)
        (simplicialColumnLinearizationHom_inclusion D R i (restrictCategoryChain f s))
    _ = (simplicialChainsFunctor R).map
        (D.map (categoryChainHeadArrow f s) ≫
          simplicialReplacementInclusion D i (restrictCategoryChain f s)) :=
      ((simplicialChainsFunctor R).map_comp _ _).symm
    _ = (simplicialChainsFunctor R).map
        (simplicialReplacementInclusion D j s ≫ simplicialReplacementMap D f) :=
      congrArg (fun t => (simplicialChainsFunctor R).map t)
        (simplicialReplacementInclusion_map D f s).symm
    _ = (simplicialChainsFunctor R).map (simplicialReplacementInclusion D j s) ≫
        (simplicialChainsFunctor R).map (simplicialReplacementMap D f) :=
      (simplicialChainsFunctor R).map_comp _ _
    _ = (chainReplacementInclusion (simplicialChainDiagram D R) j s ≫
        simplicialColumnLinearizationHom D R j) ≫
        (simplicialChainsFunctor R).map (simplicialReplacementMap D f) :=
      congrArg (fun t => t ≫ (simplicialChainsFunctor R).map (simplicialReplacementMap D f))
        (simplicialColumnLinearizationHom_inclusion D R j s).symm
    _ = _ := Category.assoc _ _ _

def simplicialReplacementLinearizationIso :
    chainReplacement (simplicialChainDiagram D R) ≅
      simplicialSetReplacement D ⋙ simplicialChainsFunctor R :=
  NatIso.ofComponents (fun i => simplicialColumnLinearizationIso D R i.unop)
    (by intro i j f; exact simplicialColumnLinearization_naturality D R f.unop)

def simplicialReplacementLinearizedBicomplex :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (AlgebraicTopology.alternatingFaceMapComplex (ChainComplex (ModuleCat.{u} R) ℕ)).obj
    (simplicialSetReplacement D ⋙ simplicialChainsFunctor R)

def simplicialReplacementBicomplexLinearizationIso :
    chainReplacementBicomplex (simplicialChainDiagram D R) ≅
      simplicialReplacementLinearizedBicomplex D R :=
  (AlgebraicTopology.alternatingFaceMapComplex (ChainComplex (ModuleCat.{u} R) ℕ)).mapIso
    (simplicialReplacementLinearizationIso D R)

def simplicialReplacementLinearizedTotal : ChainComplex (ModuleCat.{u} R) ℕ :=
  (simplicialReplacementLinearizedBicomplex D R).total (ComplexShape.down ℕ)

def simplicialReplacementTotalLinearizationIso :
    chainReplacementTotal (simplicialChainDiagram D R) ≅
      simplicialReplacementLinearizedTotal D R :=
  HomologicalComplex₂.total.mapIso (simplicialReplacementBicomplexLinearizationIso D R)
    (ComplexShape.down ℕ)

end Sharpness
