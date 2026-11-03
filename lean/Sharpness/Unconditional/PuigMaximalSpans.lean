import Sharpness.Unconditional.PuigProductDecomposition
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finset.Max

/-! Finite maximal-extension existence for spans in an EI category equipped
with an increasing finite rank. In the centric fusion orbit category the
rank is the cardinality of the source subgroup. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {C : Type u} [Category.{u} C] {P Q : C}

/-- A pair of maps with a common source. -/
structure PuigSpan (P Q : C) where
  apex : C
  left : apex ⟶ P
  right : apex ⟶ Q

namespace PuigSpan

structure Factor (A B : PuigSpan P Q) where
  hom : A.apex ⟶ B.apex
  left_fac : hom ≫ B.left = A.left
  right_fac : hom ≫ B.right = A.right

def Factor.id (A : PuigSpan P Q) : A.Factor A where
  hom := 𝟙 A.apex
  left_fac := Category.id_comp _
  right_fac := Category.id_comp _

def Factor.comp {A B D : PuigSpan P Q} (f : A.Factor B) (g : B.Factor D) : A.Factor D where
  hom := f.hom ≫ g.hom
  left_fac := by rw [Category.assoc, g.left_fac, f.left_fac]
  right_fac := by rw [Category.assoc, g.right_fac, f.right_fac]

def Maximal (A : PuigSpan P Q) : Prop := ∀ (B : PuigSpan P Q) (f : A.Factor B), IsIso f.hom

instance [Finite C] [∀ X Y : C, Finite (X ⟶ Y)] : Finite (PuigSpan P Q) := by
  apply Finite.of_injective (fun A : PuigSpan P Q =>
    (⟨A.apex, A.left, A.right⟩ : Σ X : C, (X ⟶ P) × (X ⟶ Q)))
  intro A B h
  cases A
  cases B
  cases h
  rfl

instance [∀ X Y : C, Finite (X ⟶ Y)] (A B : PuigSpan P Q) : Finite (A.Factor B) := by
  apply Finite.of_injective (fun f : A.Factor B => f.hom)
  intro f g h
  cases f
  cases g
  cases h
  rfl

/-- Maximizing source rank gives a maximal common extension. -/
theorem exists_maximal_extension [Finite C] [∀ X Y : C, Finite (X ⟶ Y)]
    (rank : C → ℕ)
    (rank_mono : ∀ {X Y : C} (f : X ⟶ Y), rank X ≤ rank Y)
    (iso_of_rank_eq : ∀ {X Y : C} (f : X ⟶ Y), rank X = rank Y → IsIso f)
    (A : PuigSpan P Q) : ∃ B : PuigSpan P Q, Nonempty (A.Factor B) ∧ B.Maximal := by
  classical
  let E := Σ B : PuigSpan P Q, A.Factor B
  letI : Fintype E := Fintype.ofFinite E
  obtain ⟨B, _, hB⟩ := Finset.exists_max_image (Finset.univ : Finset E)
    (fun B => rank B.1.apex) ⟨⟨A, Factor.id A⟩, Finset.mem_univ _⟩
  refine ⟨B.1, ⟨B.2⟩, ?_⟩
  intro D f
  exact iso_of_rank_eq f.hom (le_antisymm (rank_mono f.hom)
    (hB ⟨D, B.2.comp f⟩ (Finset.mem_univ _)))

end PuigSpan
end Sharpness
