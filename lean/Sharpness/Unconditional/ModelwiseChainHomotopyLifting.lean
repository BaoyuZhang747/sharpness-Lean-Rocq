import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Tactic.Abel

/-! The inductive algebraic step in acyclic models. It uses lifts of positive
cycles from each source degree and a degree-zero boundary. Modelwise freeness
and exactness supply these lifts in the separate presentation adapter. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness.AcyclicModels
open CategoryTheory CategoryTheory.Limits
variable {V : Type u} [Category.{v} V] [Preadditive V]
    {P Q : ChainComplex V ℕ}

def nullHomotopyOfCycleLifts (e : P ⟶ Q)
    (zero : P.X 0 ⟶ Q.X 1) (hzero : e.f 0 = zero ≫ Q.d 1 0)
    (hlift : ∀ (n : ℕ) (c : P.X (n + 1) ⟶ Q.X (n + 1)),
      c ≫ Q.d (n + 1) n = 0 →
        ∃ h : P.X (n + 1) ⟶ Q.X (n + 2), h ≫ Q.d (n + 2) (n + 1) = c) :
    Homotopy e 0 := by
  classical
  have hc₁ : (e.f 1 - P.d 1 0 ≫ zero) ≫ Q.d 1 0 = 0 := by
    rw [Preadditive.sub_comp, e.comm 1 0, hzero, Category.assoc, sub_self]
  let one := Classical.choose (hlift 0 (e.f 1 - P.d 1 0 ≫ zero) hc₁)
  have hone : one ≫ Q.d 2 1 = e.f 1 - P.d 1 0 ≫ zero :=
    Classical.choose_spec (hlift 0 (e.f 1 - P.d 1 0 ≫ zero) hc₁)
  refine Homotopy.mkInductive e zero hzero one ?_ ?_
  · rw [hone]
    abel
  · intro n p
    rcases p with ⟨a, b, hp⟩
    have hc : (e.f (n + 2) - P.d (n + 2) (n + 1) ≫ b) ≫
        Q.d (n + 2) (n + 1) = 0 := by
      rw [Preadditive.sub_comp, e.comm (n + 2) (n + 1), hp]
      simp only [Preadditive.comp_add, ← Category.assoc, P.d_comp_d,
        zero_comp, zero_add, sub_self]
    let next := Classical.choose
      (hlift (n + 1) (e.f (n + 2) - P.d (n + 2) (n + 1) ≫ b) hc)
    have hnext : next ≫ Q.d (n + 3) (n + 2) =
        e.f (n + 2) - P.d (n + 2) (n + 1) ≫ b :=
      Classical.choose_spec
        (hlift (n + 1) (e.f (n + 2) - P.d (n + 2) (n + 1) ≫ b) hc)
    refine ⟨next, ?_⟩
    rw [hnext]
    abel

end Sharpness.AcyclicModels
