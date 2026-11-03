import Mathlib

/-!
Compatible families and stable elements on an actual small category.
The stable condition in this file is imposed on all arrows of that category.
For the centric orbit category, extending this condition to all subgroup
isomorphisms requires the separate Alperin factorisation argument.
-/

set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
open CategoryTheory

structure Coefficient (R : Type u) [Ring R] (C : Type v) [Category.{v} C] where
  Value : C → Type w
  valueAddCommGroup : ∀ P, AddCommGroup (Value P)
  valueModule : ∀ P, Module R (Value P)
  pull : ∀ {P Q : C}, (P ⟶ Q) → Value Q →ₗ[R] Value P
  pull_id : ∀ P, pull (𝟙 P) = LinearMap.id
  pull_comp : ∀ {P Q T : C} (f : P ⟶ Q) (g : Q ⟶ T),
    pull (f ≫ g) = (pull f).comp (pull g)

attribute [instance] Coefficient.valueAddCommGroup Coefficient.valueModule

namespace Coefficient
variable {R : Type u} [Ring R] {C : Type v} [Category.{v} C]
    (D : Coefficient.{u,v,w} R C)

/-- The module of compatible families, with its actual equalizer equations. -/
def limit : Submodule R (∀ P, D.Value P) where
  carrier := {x | ∀ {P Q : C} (f : P ⟶ Q), D.pull f (x Q) = x P}
  zero_mem' := by
    intro P Q f
    exact map_zero (D.pull f)
  add_mem' := by
    intro x y hx hy P Q f
    change D.pull f (x Q + y Q) = x P + y P
    rw [map_add, hx f, hy f]
  smul_mem' := by
    intro a x hx P Q f
    change D.pull f (a • x Q) = a • x P
    rw [map_smul, hx f]

variable (T : C) (inc : ∀ P : C, P ⟶ T)

def arrowStable : Submodule R (D.Value T) where
  carrier := {x | ∀ {P Q : C} (f : P ⟶ Q),
    D.pull f (D.pull (inc Q) x) = D.pull (inc P) x}
  zero_mem' := by
    intro P Q f
    simp
  add_mem' := by
    intro x y hx hy P Q f
    rw [map_add, map_add, map_add, hx f, hy f]
  smul_mem' := by
    intro a x hx P Q f
    rw [map_smul, map_smul, map_smul, hx f]

theorem component_from_top (x : D.limit) (P : C) :
    D.pull (inc P) (x.val T) = x.val P := x.property (inc P)

/-- The explicit epsilon/eta isomorphism in `lem:stable-elements`, at the
level of all morphisms of the indexing category. -/
def limitEquivArrowStable (inc_id : inc T = 𝟙 T) :
    D.limit ≃ₗ[R] D.arrowStable T inc where
  toFun x := ⟨x.val T, by
    intro P Q f
    rw [D.component_from_top T inc x Q, D.component_from_top T inc x P]
    exact x.property f⟩
  invFun x := ⟨fun P => D.pull (inc P) x.val, x.property⟩
  left_inv x := by
    apply Subtype.ext
    funext P
    exact D.component_from_top T inc x P
  right_inv x := by
    apply Subtype.ext
    change D.pull (inc T) x.val = x.val
    rw [inc_id, D.pull_id]
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem limit_zero_of_arrowStable_zero
    (inc_id : inc T = 𝟙 T)
    (zero : ∀ x : D.arrowStable T inc, x.val = 0) :
    ∀ x : D.limit, x.val = 0 := by
  intro x
  have ht : x.val T = 0 := zero (D.limitEquivArrowStable T inc inc_id x)
  funext P
  have hp := D.component_from_top T inc x P
  rw [ht, map_zero] at hp
  exact hp.symm

end Coefficient
end Sharpness
