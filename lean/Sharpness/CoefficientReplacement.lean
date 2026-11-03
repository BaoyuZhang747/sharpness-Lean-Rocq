import Sharpness.CategoryChains
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-! The actual coefficient cochain complex on the indexing category:
products over all strings, with the actual head-arrow cofaces and
their alternating differential. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (M : Cᵒᵖ ⥤ ModuleCat.{u} R)

def coefficientReplacementMap {i j : SimplexCategory} (f : i ⟶ j) :
    ModuleCat.of R (∀ s : ComposableArrows C i.len, M.obj (op (chainHead s))) ⟶
      ModuleCat.of R (∀ s : ComposableArrows C j.len, M.obj (op (chainHead s))) :=
  ModuleCat.ofHom (LinearMap.pi (fun s =>
    (M.map (categoryChainHeadArrow f s).op).hom.comp (LinearMap.proj (restrictCategoryChain f s))))

def coefficientReplacement : CosimplicialObject (ModuleCat.{u} R) where
  obj i := ModuleCat.of R (∀ s : ComposableArrows C i.len, M.obj (op (chainHead s)))
  map := coefficientReplacementMap M
  map_id i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext s
    change M.map (categoryChainHeadArrow (𝟙 i) s).op (x s) = x s
    rw [categoryChainHeadArrow_id]
    change M.map (𝟙 (op (chainHead s))) (x s) = x s
    rw [M.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext s
    change M.map (categoryChainHeadArrow (f ≫ g) s).op
        (x (restrictCategoryChain (f ≫ g) s)) =
      M.map (categoryChainHeadArrow g s).op
        (M.map (categoryChainHeadArrow f (restrictCategoryChain g s)).op
          (x (restrictCategoryChain f (restrictCategoryChain g s))))
    have hd : M.map (categoryChainHeadArrow (f ≫ g) s).op =
        M.map (categoryChainHeadArrow f (restrictCategoryChain g s)).op ≫
          M.map (categoryChainHeadArrow g s).op :=
      (congrArg (fun t => M.map t.op) (categoryChainHeadArrow_comp f g s)).trans (M.map_comp _ _)
    exact congrArg (fun a => a (x (restrictCategoryChain (f ≫ g) s))) hd

def coefficientCochains : CochainComplex (ModuleCat.{u} R) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u} R)).obj (coefficientReplacement M)

end Sharpness
