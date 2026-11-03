import Sharpness.Unconditional.ModelwiseChainMap

/-! The common degree-zero-equality form of the acyclic-model comparison. -/
set_option autoImplicit false
noncomputable section
universe u v w r t
namespace Sharpness.AcyclicModels
open CategoryTheory
variable {C : Type u} [Category.{v} C] {R : Type r} [Ring R]
    {P Q : ChainComplex (C ⥤ ModuleCat.{w} R) ℕ}
    {I : ℕ → Type t} (models : ∀ n, I n → C)
    (pres : ∀ n, ModelPresentation (P.X n) (models n))

def modelwiseHomotopyOfDegreeZeroEq (f g : P ⟶ Q)
    (hmodels : ∀ n i, (modelChainComplex Q (models (n + 1) i)).ExactAt (n + 1))
    (hzero : f.f 0 = g.f 0) : Homotopy f g :=
  modelwiseHomotopy models pres f g hmodels (by
    intro i
    refine ⟨0, ?_⟩
    change (Q.d 1 0).app (models 0 i) 0 =
      ((f.f 0).app (models 0 i) - (g.f 0).app (models 0 i)) ((pres 0).generator i)
    rw [hzero]
    simp)

end Sharpness.AcyclicModels
