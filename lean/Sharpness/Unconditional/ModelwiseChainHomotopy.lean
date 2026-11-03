import Sharpness.Unconditional.ModelwiseChainHomotopyLifting
import Sharpness.Unconditional.ModelwisePresentation
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! Acyclic-model homotopies from actual free model presentations. Exactness
is required only at the models presenting the corresponding source degrees;
the target complex is not assumed acyclic on arbitrary objects. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w r t
namespace Sharpness.AcyclicModels
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] {R : Type r} [Ring R]

abbrev modelChainComplex (Q : ChainComplex (C ⥤ ModuleCat.{w} R) ℕ) (X : C) :
    ChainComplex (ModuleCat.{w} R) ℕ :=
  (((evaluation C (ModuleCat.{w} R)).obj X).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q

theorem positiveBoundaryOfExactAt (Q : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ)
    (hQ : Q.ExactAt (n + 1)) (x : Q.X (n + 1)) (hx : Q.d (n + 1) n x = 0) :
    ∃ y : Q.X (n + 2), Q.d (n + 2) (n + 1) y = x := by
  have hp : (ComplexShape.down ℕ).prev (n + 1) = n + 2 :=
    (ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl)
  have hn : (ComplexShape.down ℕ).next (n + 1) = n :=
    (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)
  have he := (Q.exactAt_iff' (n + 2) (n + 1) n hp hn).mp hQ
  exact (ShortComplex.moduleCat_exact_iff _).mp he x hx

variable {P Q : ChainComplex (C ⥤ ModuleCat.{w} R) ℕ}
    {I : ℕ → Type t} (models : ∀ n, I n → C)
    (pres : ∀ n, ModelPresentation (P.X n) (models n))

/-- Natural null homotopy from modelwise positive exactness and actual
degree-zero boundaries of the given map on the model generators. -/
def modelwiseNullHomotopy (e : P ⟶ Q)
    (hmodels : ∀ n i, (modelChainComplex Q (models (n + 1) i)).ExactAt (n + 1))
    (hzero : ∀ i, ∃ y : (Q.X 1).obj (models 0 i),
      (Q.d 1 0).app (models 0 i) y =
        (e.f 0).app (models 0 i) ((pres 0).generator i)) : Homotopy e 0 := by
  let zero := (pres 0).liftAlong (Q.d 1 0) (e.f 0) hzero
  have hz : e.f 0 = zero ≫ Q.d 1 0 := ((pres 0).liftAlong_comp _ _ hzero).symm
  refine nullHomotopyOfCycleLifts e zero hz ?_
  intro n c hc
  have hpre : ∀ i, ∃ y : (Q.X (n + 2)).obj (models (n + 1) i),
      (Q.d (n + 2) (n + 1)).app (models (n + 1) i) y =
        c.app (models (n + 1) i) ((pres (n + 1)).generator i) := by
    intro i
    apply positiveBoundaryOfExactAt (modelChainComplex Q (models (n + 1) i)) n
      (hmodels n i)
    have h := congrArg (fun f => f.app (models (n + 1) i)
      ((pres (n + 1)).generator i)) hc
    exact h
  exact ⟨(pres (n + 1)).liftAlong (Q.d (n + 2) (n + 1)) c hpre,
    (pres (n + 1)).liftAlong_comp _ _ hpre⟩

def modelwiseHomotopy (f g : P ⟶ Q)
    (hmodels : ∀ n i, (modelChainComplex Q (models (n + 1) i)).ExactAt (n + 1))
    (hzero : ∀ i, ∃ y : (Q.X 1).obj (models 0 i),
      (Q.d 1 0).app (models 0 i) y =
        ((f - g).f 0).app (models 0 i) ((pres 0).generator i)) : Homotopy f g :=
  Homotopy.equivSubZero.symm (modelwiseNullHomotopy models pres (f - g) hmodels hzero)

end Sharpness.AcyclicModels
