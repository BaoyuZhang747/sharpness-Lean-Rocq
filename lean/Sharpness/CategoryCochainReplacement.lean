import Sharpness.ProductCochains
import Sharpness.CategoryChains
import Sharpness.CochainNatTotalSigns
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.TotalComplex

/-! Actual cosimplicial replacement for a contravariant cochain diagram.
Its (i,n)-term is the product over actual strings P0 -> ... -> Pi of
D(P0)^n. Order maps restrict the string and apply its head arrow.
The alternating cofaces supply the horizontal differential; the
vertical differential is pointwise. Both squares and commutation
follow from the constructed functor, not extra input fields. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (D : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ)

def cochainReplacementColumn (i : SimplexCategory) : CochainComplex (ModuleCat.{u} R) ℕ :=
  productCochains (fun s : ComposableArrows C i.len => D.obj (op (chainHead s)))

def cochainReplacementMap {i j : SimplexCategory} (f : i ⟶ j) :
    cochainReplacementColumn D i ⟶ cochainReplacementColumn D j :=
  productCochainsMap _ _ (restrictCategoryChain f)
    (fun s => D.map (categoryChainHeadArrow f s).op)

theorem cochainReplacementMap_apply {i j : SimplexCategory} (f : i ⟶ j) (n : ℕ)
    (x : (cochainReplacementColumn D i).X n) (s : ComposableArrows C j.len) :
    (cochainReplacementMap D f).f n x s =
      (D.map (categoryChainHeadArrow f s).op).f n (x (restrictCategoryChain f s)) := rfl

def cochainReplacement : CosimplicialObject (CochainComplex (ModuleCat.{u} R) ℕ) where
  obj := cochainReplacementColumn D
  map := cochainReplacementMap D
  map_id i := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext s
    change (D.map (categoryChainHeadArrow (𝟙 i) s).op).f n (x s) = x s
    rw [categoryChainHeadArrow_id]
    change (D.map (𝟙 (op (chainHead s)))).f n (x s) = x s
    rw [D.map_id]
    rfl
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext s
    change (D.map (categoryChainHeadArrow (f ≫ g) s).op).f n
        (x (restrictCategoryChain (f ≫ g) s)) =
      (D.map (categoryChainHeadArrow g s).op).f n
        ((D.map (categoryChainHeadArrow f (restrictCategoryChain g s)).op).f n
          (x (restrictCategoryChain f (restrictCategoryChain g s))))
    have hd : D.map (categoryChainHeadArrow (f ≫ g) s).op =
        D.map (categoryChainHeadArrow f (restrictCategoryChain g s)).op ≫
          D.map (categoryChainHeadArrow g s).op :=
      (congrArg (fun t => D.map t.op) (categoryChainHeadArrow_comp f g s)).trans
        (D.map_comp _ _)
    exact congrArg (fun a => a.f n (x (restrictCategoryChain (f ≫ g) s))) hd

def cochainReplacementBicomplex :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  (AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} R) ℕ)).obj
    (cochainReplacement D)

def cochainReplacementTotal : CochainComplex (ModuleCat.{u} R) ℕ :=
  (cochainReplacementBicomplex D).total (ComplexShape.up ℕ)

end Sharpness
