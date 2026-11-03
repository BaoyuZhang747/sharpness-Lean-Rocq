import Sharpness.ColumnSpectralSequence

/-! The differential of the actual native first page is the connecting
map between its adjacent relative terms. All filtration indices and
cohomological degrees are fixed explicitly. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian.SpectralObject
variable {C : Type u} [Category.{v} C] [Abelian C]
    (X : Abelian.SpectralObject C ℕᵒᵈ) [ColumnSpectralSupport X]

set_option backward.isDefEq.respectTransparency false in
theorem columnSpectralSequence_first_d_eq (p q : ℕ) :
    ((columnSpectralSequence X).page 1).d (p,q) (p+1,q) =
      (columnSpectralSequenceFirstPageIso X p q).hom ≫
        X.δ
          (homOfLE (show OrderDual.toDual (p+2) ≤ OrderDual.toDual (p+1) from Nat.le_succ (p+1)))
          (homOfLE (show OrderDual.toDual (p+1) ≤ OrderDual.toDual p from Nat.le_succ p))
          ((p : ℤ)+q) (((p+1 : ℕ) : ℤ)+q) (by omega) ≫
        (columnSpectralSequenceFirstPageIso X (p+1) q).inv := by
  exact X.spectralSequence_first_page_d_eq columnSpectralCore (p,q) (p+1,q)
    (by simp only [ComplexShape.spectralSequenceNat_rel_iff]; constructor <;> omega)
    (OrderDual.toDual (p+2)) (OrderDual.toDual (p+1)) (OrderDual.toDual p) rfl rfl rfl
    ((p : ℤ)+q) (((p+1 : ℕ) : ℤ)+q) rfl (by omega)

end Sharpness
