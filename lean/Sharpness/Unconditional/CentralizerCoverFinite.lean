import Sharpness.Unconditional.CentralizerCoverFibration

/-! Finiteness of the concrete base and total categories in the centralizer
fibration, including the fully centralized object wrappers. -/

set_option autoImplicit false
noncomputable section

universe u
namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S) (p : ℕ)

instance elementaryCategoryFinite : Finite (F.ElementaryCategory p) := by
  apply Finite.of_injective (fun E : F.ElementaryCategory p => E.obj)
  intro E D h
  cases E
  cases D
  cases h
  rfl

instance elementaryCategoryHomFinite (E D : F.ElementaryCategory p) : Finite (E ⟶ D) :=
  Finite.of_injective (fun f : E ⟶ D => f.hom) (fun _ _ h => InducedCategory.hom_ext h)

instance centralizedCentralizerCoverFinite : Finite (F.CentralizedCentralizerCover p) := by
  apply Finite.of_injective (fun A : F.CentralizedCentralizerCover p => A.obj)
  intro A B h
  cases A
  cases B
  cases h
  rfl

instance centralizedCentralizerCoverHomFinite (A B : F.CentralizedCentralizerCover p) :
    Finite (A ⟶ B) :=
  Finite.of_injective (fun f : A ⟶ B => f.hom) (fun _ _ h => InducedCategory.hom_ext h)

end Sharpness.FusionSystem
