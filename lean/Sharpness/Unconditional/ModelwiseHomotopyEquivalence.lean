import Sharpness.Unconditional.ModelwiseChainComparison
import Mathlib.Algebra.Homology.QuasiIso

/-! A comparison is a homotopy equivalence when its inverse extends from
degree zero and both comparison homotopies are supplied by acyclic models. -/
set_option autoImplicit false
noncomputable section
universe u v w r t s
namespace Sharpness.AcyclicModels
open CategoryTheory
variable {C : Type u} [Category.{v} C] {R : Type r} [Ring R]
    {P Q : ChainComplex (C ⥤ ModuleCat.{w} R) ℕ}
    {I : ℕ → Type t} {J : ℕ → Type s}
    (modelsP : ∀ n, I n → C) (modelsQ : ∀ n, J n → C)
    (presP : ∀ n, ModelPresentation (P.X n) (modelsP n))
    (presQ : ∀ n, ModelPresentation (Q.X n) (modelsQ n))
    (f : P ⟶ Q) (e₀ : P.X 0 ≅ Q.X 0) (hf₀ : f.f 0 = e₀.hom)
    (hP : ∀ n i, (modelChainComplex P (modelsP (n + 1) i)).ExactAt (n + 1))
    (hQ : ∀ n j, (modelChainComplex Q (modelsQ (n + 1) j)).ExactAt (n + 1))
    (hcross : ∀ n j, (modelChainComplex P (modelsQ (n + 2) j)).ExactAt (n + 1))
    (h₁ : ∀ j, ∃ y : (P.X 1).obj (modelsQ 1 j),
      (P.d 1 0).app (modelsQ 1 j) y =
        (Q.d 1 0 ≫ e₀.inv).app (modelsQ 1 j) ((presQ 1).generator j))

def modelwiseHomotopyEquivalence : HomotopyEquiv P Q where
  hom := f
  inv := modelwiseChainMap modelsQ presQ e₀.inv hcross h₁
  homotopyHomInvId := modelwiseHomotopyOfDegreeZeroEq modelsP presP _ _ hP (by
    change f.f 0 ≫ (modelwiseChainMap modelsQ presQ e₀.inv hcross h₁).f 0 = 𝟙 _
    rw [hf₀, modelwiseChainMap_zero, e₀.hom_inv_id])
  homotopyInvHomId := modelwiseHomotopyOfDegreeZeroEq modelsQ presQ _ _ hQ (by
    change (modelwiseChainMap modelsQ presQ e₀.inv hcross h₁).f 0 ≫ f.f 0 = 𝟙 _
    rw [modelwiseChainMap_zero, hf₀, e₀.inv_hom_id])

include modelsP modelsQ presP presQ e₀ hf₀ hP hQ hcross h₁ in
theorem quasiIso_of_modelwise_comparison : QuasiIso f :=
  (modelwiseHomotopyEquivalence modelsP modelsQ presP presQ f e₀ hf₀
    hP hQ hcross h₁).quasiIso_hom

end Sharpness.AcyclicModels
