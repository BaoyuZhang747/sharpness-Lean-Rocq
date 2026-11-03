import Sharpness.Unconditional.ChainTotalFiniteProjections

/-! Actual two-component incoming differentials on a first-quadrant total. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits

variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))

theorem chainTotal_horizontal_incoming (p q n : ℕ) (hpq : p + q = n) :
    K.D₁ (ComplexShape.down ℕ) (n + 1) n ≫ chainTotalProjection K p q n hpq =
      chainTotalProjection K (p + 1) q (n + 1) (by omega) ≫ (K.d (p + 1) p).f q := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i + j = n + 1 at hij
  rw [← Category.assoc, ← Category.assoc]
  cases i with
  | zero =>
      rw [chainTotal_horizontal_zero_outgoing K j n hij, zero_comp,
        chainTotalProjection_other K (p + 1) q (n + 1) 0 j (by omega) hij (by omega),
        zero_comp]
  | succ i =>
      rw [chainTotal_horizontal_outgoing K i j n (by omega), Category.assoc]
      by_cases hi : i = p
      · subst i
        have hj : j = q := by omega
        subst j
        rw [chainTotalProjection_inclusion, chainTotalProjection_inclusion,
          Category.comp_id, Category.id_comp]
      · rw [chainTotalProjection_other K p q n i j hpq (by omega) hi, comp_zero,
          chainTotalProjection_other K (p + 1) q (n + 1) (i + 1) j
            (by omega) hij (by omega), zero_comp]

theorem chainTotal_vertical_incoming (p q n : ℕ) (hpq : p + q = n) :
    K.D₂ (ComplexShape.down ℕ) (n + 1) n ≫ chainTotalProjection K p q n hpq =
      (-1 : ℤˣ) ^ p •
        (chainTotalProjection K p (q + 1) (n + 1) (by omega) ≫ (K.X p).d (q + 1) q) := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i + j = n + 1 at hij
  rw [← Category.assoc, Linear.comp_units_smul, ← Category.assoc]
  cases j with
  | zero =>
      rw [chainTotal_vertical_zero_outgoing K i n hij, zero_comp,
        chainTotalProjection_other K p (q + 1) (n + 1) i 0 (by omega) hij (by omega),
        zero_comp, smul_zero]
  | succ j =>
      rw [chainTotal_vertical_outgoing K i j n (by omega), Linear.units_smul_comp, Category.assoc]
      by_cases hi : i = p
      · subst i
        have hj : j = q := by omega
        subst j
        rw [chainTotalProjection_inclusion, chainTotalProjection_inclusion,
          Category.comp_id, Category.id_comp]
      · rw [chainTotalProjection_other K p q n i j hpq (by omega) hi, comp_zero,
          chainTotalProjection_other K p (q + 1) (n + 1) i (j + 1)
            (by omega) hij hi, zero_comp, smul_zero, smul_zero]

end Sharpness
