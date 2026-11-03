import Sharpness.AlexanderWhitneyFaces
import Sharpness.SimplicialReplacementInclusions
import Sharpness.EilenbergZilberInput

/-! The horizontal-zero Alexander–Whitney component on the actual
replacement retains the head object and the original vertical
simplex. This calculation is proved from the explicit order maps,
not added to the general reference input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C : Type u} [Category.{u} C] (D : C ⥤ SSet.{u})

theorem restrictCategoryChain_headVertex (n : ℕ) (s : ComposableArrows C n) :
    restrictCategoryChain (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) s =
      ComposableArrows.mk₀ (chainHead s) :=
  ComposableArrows.ext₀ rfl

theorem categoryChainHeadArrow_headVertex (n : ℕ) (s : ComposableArrows C n) :
    categoryChainHeadArrow (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) s = 𝟙 (chainHead s) :=
  s.map_id _

theorem simplicialReplacement_headVertex (n : ℕ) (s : ComposableArrows C n)
    (x : (D.obj (chainHead s)).obj (op ⦋n⦌)) :
    (simplicialReplacementMap D (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)).app (op ⦋n⦌) ⟨s, x⟩ =
      replacementSimplex D ⦋0⦌ (op ⦋n⦌) (ComposableArrows.mk₀ (chainHead s)) x := by
  have hd : D.map (categoryChainHeadArrow (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) s) =
      𝟙 (D.obj (chainHead s)) :=
    (congrArg (fun f => D.map f) (categoryChainHeadArrow_headVertex n s)).trans (D.map_id _)
  have hx := congrArg (fun t => t.app (op ⦋n⦌) x) hd
  change replacementSimplex D ⦋0⦌ (op ⦋n⦌)
      (restrictCategoryChain (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) s)
      ((D.map (categoryChainHeadArrow (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) s)).app (op ⦋n⦌) x) = _
  rw [hx]
  exact Sigma.ext (restrictCategoryChain_headVertex n s) (HEq.rfl)

theorem replacementAlexanderWhitneySimplex_zero (n : ℕ) (h : 0+n=n)
    (s : ComposableArrows C n) (x : (D.obj (chainHead s)).obj (op ⦋n⦌)) :
    alexanderWhitneySimplex (simplicialSetReplacement D) 0 n n h ⟨s, x⟩ =
      replacementSimplex D ⦋0⦌ (op ⦋n⦌) (ComposableArrows.mk₀ (chainHead s)) x := by
  rw [alexanderWhitneySimplex_zero]
  exact simplicialReplacement_headVertex D n s x

theorem replacementAlexanderWhitney_zeroColumn {R : Type u} [CommRing R]
    (ez : EilenbergZilberInput.{u} R) (n : ℕ) (h : 0+n=n)
    (s : ComposableArrows C n) (x : (D.obj (chainHead s)).obj (op ⦋n⦌)) :
    (bisimplicialDiagonal (simplicialSetReplacement D)).ιChainComplex (R := ModuleCat.of R R) ⟨s, x⟩ ≫
        (ez.alexanderWhitney (simplicialSetReplacement D)).f n ≫
        chainTotalProjection (bisimplicialChainBicomplex (simplicialSetReplacement D) R) 0 n n h =
      (simplicialReplacementColumn D ⦋0⦌).ιChainComplex
        (replacementSimplex D ⦋0⦌ (op ⦋n⦌) (ComposableArrows.mk₀ (chainHead s)) x) := by
  rw [ez.alexanderWhitney_component, replacementAlexanderWhitneySimplex_zero]
  rfl

end Sharpness
