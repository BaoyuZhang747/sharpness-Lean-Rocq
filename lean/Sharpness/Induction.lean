import Mathlib

/-!
The numerical and well-founded induction steps in the main proof.
`central_quotient_induction` is a proof architecture theorem, not the
Díaz--Park theorem for actual saturated fusion systems: its two reduction
hypotheses are original results of the manuscript and must still be supplied.
-/

set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness

theorem quotient_card_lt (G : Type u) [Group G] [Finite G]
    (Z : Subgroup G) [Z.Normal] (hZ : 1 < Nat.card Z) :
    Nat.card (G ⧸ Z) < Nat.card G := by
  have hmul := Z.card_mul_index
  have hpos : 0 < Z.index := Nat.card_pos
  have hlt : Z.index < Nat.card Z * Z.index := by
    simpa using Nat.mul_lt_mul_of_pos_right hZ hpos
  calc
    Nat.card (G ⧸ Z) = Z.index := Z.index_eq_card.symm
    _ < Nat.card Z * Z.index := hlt
    _ = Nat.card G := hmul

/-- The estimate also covers the important case where the centralizer is
the whole Sylow group. No strict decrease of the centralizer is assumed. -/
theorem quotient_card_lt_ambient (S : Type u) [Group S] [Finite S]
    (T : Subgroup S) (Z : Subgroup T) [Z.Normal] (hZ : 1 < Nat.card Z) :
    Nat.card (T ⧸ Z) < Nat.card S := by
  exact lt_of_lt_of_le (quotient_card_lt T Z hZ)
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

/-- All the structural data in the cardinal induction. The entries are
independent of the property being proved. -/
structure CentralizerDiagram (F : Type u) where
  order : F → ℕ
  Elementary : F → Type v
  centralizer : (f : F) → Elementary f → F
  quotient : (f : F) → Elementary f → F
  quotient_smaller : ∀ f e, order (quotient f e) < order f

/-- Checked logical assembly of the last proof in Section 3.
`central_lift` corresponds to `prop:central` and `criterion` to
`thm:criterion`. They are not classified as literature assumptions. -/
theorem central_quotient_induction {F : Type u} (D : CentralizerDiagram.{u,v} F)
    (P : F → Prop)
    (base : ∀ f, D.order f ≤ 1 → P f)
    (central_lift : ∀ f e, P (D.quotient f e) → P (D.centralizer f e))
    (criterion : ∀ f, 1 < D.order f → (∀ e, P (D.centralizer f e)) → P f) :
    ∀ f, P f := by
  have aux : ∀ n, ∀ f, D.order f = n → P f := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf
      by_cases hn : n ≤ 1
      · exact base f (hf ▸ hn)
      · apply criterion f (by omega)
        intro e
        apply central_lift f e
        exact ih (D.order (D.quotient f e)) (hf ▸ D.quotient_smaller f e)
          (D.quotient f e) rfl
  intro f
  exact aux (D.order f) f rfl

end Sharpness
