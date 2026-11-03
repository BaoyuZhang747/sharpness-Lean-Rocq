import Sharpness.FiniteBar
import Sharpness.CoefficientCochainFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! The finite bar model is the actual alternating coefficient complex.
Finiteness comes from the finiteness of the objects and morphisms of the
indexing category, without any homological input. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits Opposite Simplicial

variable {R C : Type u} [CommRing R] [Category.{u} C]

/-- A finite category has finitely many strings of each fixed length. -/
instance finiteComposableArrows [Finite C] [∀ X Y : C, Finite (X ⟶ Y)] (n : ℕ) :
    Finite (ComposableArrows C n) := by
  let enc : ComposableArrows C n →
      Σ f : Fin (n + 1) → C, ∀ i j, (i ⟶ j) → (f i ⟶ f j) :=
    fun F => ⟨F.obj, @F.map⟩
  apply Finite.of_injective enc
  intro F G h
  cases F
  cases G
  cases h
  rfl

/-- The concrete coefficient cochains, indexed by all composable arrows. -/
def finiteCategoryBarModel (R C : Type u) [CommRing R] [Category.{u} C]
    [Finite C] [∀ X Y : C, Finite (X ⟶ Y)] : FiniteBarModel R C where
  Index n := ComposableArrows C n
  finiteIndex n := Fintype.ofFinite _
  source n s := op (s.obj 0)
  d M n := ((coefficientCochains M).d n (n + 1)).hom
  dd M n := by
    exact congrArg ModuleCat.Hom.hom ((coefficientCochains M).d_comp_d n (n + 1) (n + 2))
  naturality {M N} a n := by
    exact congrArg ModuleCat.Hom.hom ((coefficientCochainFunctor.map a).comm n (n + 1))

/-- Native module homology is the concrete cycles modulo boundaries used in
the original finite bar interface. -/
def finiteCategoryBarCohomologyIso [Finite C] [∀ X Y : C, Finite (X ⟶ Y)]
    (M : CoefficientCategory R C) (n : ℕ) :
    (coefficientCochains M).homology (n + 1) ≅
      ModuleCat.of R ((finiteCategoryBarModel R C).Cohomology M n) :=
  (coefficientCochains M).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp) ≪≫
    ((coefficientCochains M).sc' n (n + 1) (n + 2)).moduleCatHomologyIso

end Sharpness.Unconditional
