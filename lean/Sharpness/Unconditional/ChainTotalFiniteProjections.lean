import Sharpness.ChainTotalProjection
import Sharpness.ChainTotalOutgoing

/-! Finite nonnegative diagonals of the actual total complex: summand
projections jointly detect maps into the total object. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits

variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))

theorem chainTotal_projection_sum (n : ℕ) :
    (∑ i : Fin (n + 1), chainTotalProjection K i.val (n - i.val) n (by omega) ≫
      K.ιTotal (ComplexShape.down ℕ) i.val (n - i.val) n
        (by change i.val + (n - i.val) = n; omega)) =
      𝟙 ((K.total (ComplexShape.down ℕ)).X n) := by
  classical
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p + q = n at hpq
  rw [comp_sum, Category.comp_id]
  let k : Fin (n + 1) := ⟨p, by omega⟩
  rw [Finset.sum_eq_single k]
  · have hq : n - p = q := by omega
    subst q
    dsimp only [k]
    rw [← Category.assoc, chainTotalProjection_inclusion, Category.id_comp]
  · intro i _ hi
    have hip : p ≠ i.val := by
      intro he
      apply hi
      exact Fin.ext he.symm
    rw [← Category.assoc, chainTotalProjection_other K i.val (n - i.val) n p q
      (by omega) hpq hip, zero_comp]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

/-- Equality into a finite diagonal is detected by all actual projections. -/
theorem chainTotal_projection_hom_ext {B : ModuleCat.{u} R} {n : ℕ}
    {f g : B ⟶ (K.total (ComplexShape.down ℕ)).X n}
    (h : ∀ p q (hpq : p + q = n),
      f ≫ chainTotalProjection K p q n hpq = g ≫ chainTotalProjection K p q n hpq) :
    f = g := by
  rw [← Category.comp_id f, ← Category.comp_id g, ← chainTotal_projection_sum K n]
  simp only [comp_sum, ← Category.assoc, h]

end Sharpness
