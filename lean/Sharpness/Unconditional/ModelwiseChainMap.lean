import Sharpness.Unconditional.ModelwiseChainHomotopy

/-! Natural chain-map extension by acyclic models. The first lift is required
only on the degree-one generators; all later lifts follow from positive
exactness of the target at the models presenting the source degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w r t
namespace Sharpness.AcyclicModels
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] {R : Type r} [Ring R]
    {P Q : ChainComplex (C ⥤ ModuleCat.{w} R) ℕ}
    {I : ℕ → Type t} (models : ∀ n, I n → C)
    (pres : ∀ n, ModelPresentation (P.X n) (models n))

def modelwiseChainMap (zero : P.X 0 ⟶ Q.X 0)
    (hmodels : ∀ n i, (modelChainComplex Q (models (n + 2) i)).ExactAt (n + 1))
    (hone : ∀ i, ∃ y : (Q.X 1).obj (models 1 i),
      (Q.d 1 0).app (models 1 i) y =
        (P.d 1 0 ≫ zero).app (models 1 i) ((pres 1).generator i)) : P ⟶ Q := by
  let one := (pres 1).liftAlong (Q.d 1 0) (P.d 1 0 ≫ zero) hone
  have h₁ : one ≫ Q.d 1 0 = P.d 1 0 ≫ zero :=
    (pres 1).liftAlong_comp _ _ hone
  refine ChainComplex.mkHom P Q zero one h₁ ?_
  intro n p
  rcases p with ⟨a, b, hp⟩
  let c := P.d (n + 2) (n + 1) ≫ b
  have hc : c ≫ Q.d (n + 1) n = 0 := by
    change (P.d (n + 2) (n + 1) ≫ b) ≫ Q.d (n + 1) n = 0
    rw [Category.assoc, hp, ← Category.assoc, P.d_comp_d, zero_comp]
  have hpre : ∀ i, ∃ y : (Q.X (n + 2)).obj (models (n + 2) i),
      (Q.d (n + 2) (n + 1)).app (models (n + 2) i) y =
        c.app (models (n + 2) i) ((pres (n + 2)).generator i) := by
    intro i
    apply positiveBoundaryOfExactAt (modelChainComplex Q (models (n + 2) i)) n
      (hmodels n i)
    exact congrArg (fun f => f.app (models (n + 2) i)
      ((pres (n + 2)).generator i)) hc
  exact ⟨(pres (n + 2)).liftAlong (Q.d (n + 2) (n + 1)) c hpre,
    (pres (n + 2)).liftAlong_comp _ _ hpre⟩

theorem modelwiseChainMap_zero (zero : P.X 0 ⟶ Q.X 0)
    (hmodels : ∀ n i, (modelChainComplex Q (models (n + 2) i)).ExactAt (n + 1))
    (hone : ∀ i, ∃ y : (Q.X 1).obj (models 1 i),
      (Q.d 1 0).app (models 1 i) y =
        (P.d 1 0 ≫ zero).app (models 1 i) ((pres 1).generator i)) :
    (modelwiseChainMap models pres zero hmodels hone).f 0 = zero := rfl

end Sharpness.AcyclicModels
