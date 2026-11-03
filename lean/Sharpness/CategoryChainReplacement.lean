import Sharpness.CoproductChainsMaps
import Sharpness.CategoryChains
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-! The covariant chain diagram gives the actual simplicial direct-sum
replacement. The head arrow acts covariantly and the order map
restricts the string. All simplicial identities are proved from the
original diagram's functor laws. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (D : C ⥤ ChainComplex (ModuleCat.{u} R) ℕ)

def chainReplacementColumn (i : SimplexCategory) : ChainComplex (ModuleCat.{u} R) ℕ :=
  coproductChains (fun s : ComposableArrows C i.len => D.obj (chainHead s))

def chainReplacementInclusion (i : SimplexCategory) (s : ComposableArrows C i.len) :
    D.obj (chainHead s) ⟶ chainReplacementColumn D i :=
  coproductChainsInclusion (fun t : ComposableArrows C i.len => D.obj (chainHead t)) s

def chainReplacementMap {i j : SimplexCategory} (f : i ⟶ j) :
    chainReplacementColumn D j ⟶ chainReplacementColumn D i :=
  coproductChainsMap _ _ (restrictCategoryChain f) (fun s => D.map (categoryChainHeadArrow f s))

@[reassoc]
theorem chainReplacementMap_inclusion {i j : SimplexCategory} (f : i ⟶ j)
    (s : ComposableArrows C j.len) :
    chainReplacementInclusion D j s ≫ chainReplacementMap D f =
      D.map (categoryChainHeadArrow f s) ≫
        chainReplacementInclusion D i (restrictCategoryChain f s) :=
  coproductChainsMap_inclusion _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem chainReplacementMap_id (i : SimplexCategory) : chainReplacementMap D (𝟙 i) = 𝟙 _ := by
  apply coproductChains_hom_ext
  intro s
  have hd : D.map (categoryChainHeadArrow (𝟙 i) s) = 𝟙 (D.obj (chainHead s)) :=
    (congrArg (fun a => D.map a) (categoryChainHeadArrow_id s)).trans (D.map_id _)
  calc
    _ = D.map (categoryChainHeadArrow (𝟙 i) s) ≫ chainReplacementInclusion D i s :=
      chainReplacementMap_inclusion D (𝟙 i) s
    _ = (𝟙 _) ≫ chainReplacementInclusion D i s :=
      congrArg (fun a => a ≫ chainReplacementInclusion D i s) hd
    _ = _ := (Category.id_comp _).trans (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
theorem chainReplacementMap_comp {i j k : SimplexCategory} (f : i ⟶ j) (g : j ⟶ k) :
    chainReplacementMap D (f ≫ g) = chainReplacementMap D g ≫ chainReplacementMap D f := by
  apply coproductChains_hom_ext
  intro s
  have hd : D.map (categoryChainHeadArrow (f ≫ g) s) =
      D.map (categoryChainHeadArrow g s) ≫ D.map (categoryChainHeadArrow f (restrictCategoryChain g s)) :=
    (congrArg (fun a => D.map a) (categoryChainHeadArrow_comp f g s)).trans (D.map_comp _ _)
  calc
    _ = D.map (categoryChainHeadArrow (f ≫ g) s) ≫
        chainReplacementInclusion D i (restrictCategoryChain (f ≫ g) s) := chainReplacementMap_inclusion D (f ≫ g) s
    _ = (D.map (categoryChainHeadArrow g s) ≫ D.map (categoryChainHeadArrow f (restrictCategoryChain g s))) ≫
        chainReplacementInclusion D i (restrictCategoryChain (f ≫ g) s) :=
      congrArg (fun t => t ≫ chainReplacementInclusion D i (restrictCategoryChain (f ≫ g) s)) hd
    _ = D.map (categoryChainHeadArrow g s) ≫
        (D.map (categoryChainHeadArrow f (restrictCategoryChain g s)) ≫
          chainReplacementInclusion D i (restrictCategoryChain f (restrictCategoryChain g s))) := Category.assoc _ _ _
    _ = (D.map (categoryChainHeadArrow g s) ≫ chainReplacementInclusion D j (restrictCategoryChain g s)) ≫
        chainReplacementMap D f :=
      (congrArg (fun t => D.map (categoryChainHeadArrow g s) ≫ t)
        (chainReplacementMap_inclusion D f (restrictCategoryChain g s)).symm).trans (Category.assoc _ _ _).symm
    _ = (chainReplacementInclusion D k s ≫ chainReplacementMap D g) ≫ chainReplacementMap D f :=
      congrArg (fun t => t ≫ chainReplacementMap D f) (chainReplacementMap_inclusion D g s).symm
    _ = _ := Category.assoc _ _ _

def chainReplacement : SimplicialObject (ChainComplex (ModuleCat.{u} R) ℕ) where
  obj i := chainReplacementColumn D i.unop
  map f := chainReplacementMap D f.unop
  map_id i := chainReplacementMap_id D i.unop
  map_comp f g := chainReplacementMap_comp D g.unop f.unop

end Sharpness
