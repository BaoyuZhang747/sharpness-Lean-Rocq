import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.Finite.Defs

/-! A finite product decomposition on an ordinary category: its representable
presheaves have a product which is a finite coproduct of representables.
Naturality is expressed by the actual structure maps of the summands. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Opposite

variable {C : Type u} [Category.{u} C]

/-- The concrete universal property needed for products in the finite
coproduct completion, before introducing that completion. -/
structure ProductDecomposition (P Q : C) where
  Index : Type u
  finiteIndex : Finite Index
  apex : Index → C
  left : ∀ i, apex i ⟶ P
  right : ∀ i, apex i ⟶ Q
  bijective : ∀ X : C, Function.Bijective
    (fun z : Σ i, X ⟶ apex i => (z.2 ≫ left z.1, z.2 ≫ right z.1))

attribute [instance] ProductDecomposition.finiteIndex

namespace ProductDecomposition
variable {P Q : C} (D : ProductDecomposition P Q)

/-- Exchange the two factors, keeping the same representable summands. -/
def swap : ProductDecomposition Q P where
  Index := D.Index
  finiteIndex := D.finiteIndex
  apex := D.apex
  left := D.right
  right := D.left
  bijective X := (Equiv.prodComm (X ⟶ P) (X ⟶ Q)).bijective.comp (D.bijective X)

def homEquiv (X : C) : (Σ i, X ⟶ D.apex i) ≃ ((X ⟶ P) × (X ⟶ Q)) :=
  Equiv.ofBijective _ (D.bijective X)

theorem homEquiv_apply (X : C) (i : D.Index) (f : X ⟶ D.apex i) :
    D.homEquiv X ⟨i, f⟩ = (f ≫ D.left i, f ≫ D.right i) := rfl

/-- Precomposition is the actual map on every representable summand. -/
theorem homEquiv_naturality {X Y : C} (f : X ⟶ Y)
    (i : D.Index) (g : Y ⟶ D.apex i) :
    D.homEquiv X ⟨i, f ≫ g⟩ =
      (f ≫ (D.homEquiv Y ⟨i, g⟩).1, f ≫ (D.homEquiv Y ⟨i, g⟩).2) := by
  exact Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

end ProductDecomposition
end Sharpness
