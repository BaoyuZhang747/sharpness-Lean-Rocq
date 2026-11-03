import Sharpness.ChainZeroColumnAugmentation
import Sharpness.SimplicialLinearizationAugmentation

/-! The actual chain cocone kills the two horizontal faces entering
column zero. This constructs its augmentation out of the entire
signed replacement total, without any geometric input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C : Type u} [Category.{u} C] (D : C ⥤ SSet.{u})
    (R : Type u) [CommRing R] {X : SSet.{u}} (a : D ⟶ (Functor.const C).obj X)

theorem simplicialChainCoconeColumn_inclusion (i : SimplexCategory)
    (s : ComposableArrows C i.len) :
    chainReplacementInclusion (simplicialChainDiagram D R) i s ≫ simplicialChainCoconeColumn D R a i =
      (simplicialChainsFunctor R).map (a.app (chainHead s)) :=
  coproductChainsInclusion_desc
    (fun t : ComposableArrows C i.len => (simplicialChainDiagram D R).obj (chainHead t))
    (fun t => (simplicialChainsFunctor R).map (a.app (chainHead t))) s

theorem simplicialChainCoconeColumn_horizontal_zero :
    (chainReplacementBicomplex (simplicialChainDiagram D R)).d 1 0 ≫
      simplicialChainCoconeColumn D R a ⦋0⦌ = 0 := by
  calc
    _ = (∑ j : Fin 2, (-1 : ℤ)^j.val •
        chainReplacementMap (simplicialChainDiagram D R) (SimplexCategory.δ j)) ≫
        simplicialChainCoconeColumn D R a ⦋0⦌ :=
      congrArg (fun f : chainReplacementColumn (simplicialChainDiagram D R) ⦋1⦌ ⟶
          chainReplacementColumn (simplicialChainDiagram D R) ⦋0⦌ =>
        f ≫ simplicialChainCoconeColumn D R a ⦋0⦌)
        (chainReplacementBicomplex_horizontal (simplicialChainDiagram D R) 0)
    _ = (chainReplacementMap (simplicialChainDiagram D R) (SimplexCategory.δ (0 : Fin 2)) ≫
        simplicialChainCoconeColumn D R a ⦋0⦌) +
        -(chainReplacementMap (simplicialChainDiagram D R) (SimplexCategory.δ (1 : Fin 2)) ≫
          simplicialChainCoconeColumn D R a ⦋0⦌) := by
      simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
        neg_one_smul, Preadditive.add_comp, Preadditive.neg_comp]
    _ = simplicialChainCoconeColumn D R a ⦋1⦌ + -simplicialChainCoconeColumn D R a ⦋1⦌ :=
      congrArg₂ (fun f g => f + -g)
        (simplicialChainCoconeColumn_naturality D R a (SimplexCategory.δ (0 : Fin 2)))
        (simplicialChainCoconeColumn_naturality D R a (SimplexCategory.δ (1 : Fin 2)))
    _ = 0 := add_neg_cancel _

def simplicialChainTotalAugmentation :
    chainReplacementTotal (simplicialChainDiagram D R) ⟶ X.chainComplex (ModuleCat.of R R) :=
  chainZeroColumnAugmentation (chainReplacementBicomplex (simplicialChainDiagram D R))
    (simplicialChainCoconeColumn D R a ⦋0⦌) (simplicialChainCoconeColumn_horizontal_zero D R a)

theorem simplicialChainTotalAugmentation_f (n : ℕ) :
    (simplicialChainTotalAugmentation D R a).f n =
      chainTotalProjection (chainReplacementBicomplex (simplicialChainDiagram D R)) 0 n n (by omega) ≫
        (simplicialChainCoconeColumn D R a ⦋0⦌).f n := rfl

end Sharpness
