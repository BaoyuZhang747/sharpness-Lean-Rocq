import Sharpness.CategoryChainReplacement
import Mathlib.Algebra.Homology.TotalComplex

/-! The actual chain replacement bicomplex and its direct-sum total
complex. Both differentials, commutation, and totalization signs come
from the constructed simplicial object and native chain totalization. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (D : C ⥤ ChainComplex (ModuleCat.{u} R) ℕ)

def chainReplacementBicomplex :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (AlgebraicTopology.alternatingFaceMapComplex (ChainComplex (ModuleCat.{u} R) ℕ)).obj (chainReplacement D)

def chainReplacementTotal : ChainComplex (ModuleCat.{u} R) ℕ :=
  (chainReplacementBicomplex D).total (ComplexShape.down ℕ)

theorem chainReplacementBicomplex_horizontal (i : ℕ) :
    (chainReplacementBicomplex D).d (i+1) i =
      ∑ j : Fin (i+2), (-1 : ℤ)^j.val • chainReplacementMap D (SimplexCategory.δ j) := by
  dsimp only [chainReplacementBicomplex, AlgebraicTopology.alternatingFaceMapComplex,
    AlgebraicTopology.AlternatingFaceMapComplex.obj]
  rw [ChainComplex.of_d]
  rfl

theorem chainReplacementBicomplex_vertical_inclusion (i n : ℕ) (s : ComposableArrows C i) :
    (chainReplacementInclusion D ⦋i⦌ s).f (n+1) ≫ ((chainReplacementBicomplex D).X i).d (n+1) n =
      (D.obj (chainHead s)).d (n+1) n ≫ (chainReplacementInclusion D ⦋i⦌ s).f n :=
  (chainReplacementInclusion D ⦋i⦌ s).comm (n+1) n

theorem chainReplacementBicomplex_comm (i n : ℕ) :
    ((chainReplacementBicomplex D).d (i+1) i).f (n+1) ≫ ((chainReplacementBicomplex D).X i).d (n+1) n =
      ((chainReplacementBicomplex D).X (i+1)).d (n+1) n ≫ ((chainReplacementBicomplex D).d (i+1) i).f n :=
  HomologicalComplex₂.d_comm _ _ _ _ _

theorem chainReplacementTotal_horizontalSign (i n : ℕ) :
    ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (i,n) = 1 := rfl

theorem chainReplacementTotal_verticalSign (i n : ℕ) :
    ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (i,n) = (-1 : ℤˣ)^i := rfl

end Sharpness
