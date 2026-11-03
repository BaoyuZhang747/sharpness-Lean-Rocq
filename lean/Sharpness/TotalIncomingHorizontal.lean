import Sharpness.ZeroColumnTotalProjection

/-! The horizontal total differential has one incoming contribution
to every positive column, and none to column zero. The proof checks
all actual total summands. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
theorem cochainTotal_horizontal_incoming (p q n : ℕ) (h : p+q=n) :
    K.D₁ (ComplexShape.up ℕ) n (n+1) ≫
        totalSummandProjectionAt K (p+1) q (n+1) (by omega) =
      totalSummandProjectionAt K p q n h ≫ (K.d p (p+1)).f q := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i+j=n at hij
  have hd : K.ιTotal (ComplexShape.up ℕ) i j n hij ≫ K.D₁ (ComplexShape.up ℕ) n (n+1) =
      (K.d i (i+1)).f j ≫ K.ιTotal (ComplexShape.up ℕ) (i+1) j (n+1) (by change i+1+j=n+1; omega) := by
    rw [HomologicalComplex₂.ι_D₁, HomologicalComplex₂.d₁_eq K (ComplexShape.up ℕ)
      (show (ComplexShape.up ℕ).Rel i (i+1) from rfl) j (n+1) (by change i+1+j=n+1; omega)]
    simp only [cochainNatTotalHorizontalSign, one_smul]
  rw [← Category.assoc, hd, Category.assoc]
  by_cases hi : i=p
  · subst i
    have hj : j=q := by omega
    subst j
    rw [totalSummandProjectionAt_inclusion, Category.comp_id, ← Category.assoc,
      totalSummandProjectionAt_inclusion, Category.id_comp]
  · rw [totalSummandProjectionAt_other K (p+1) q (n+1) (i+1) j (by omega) (by omega) (by omega),
      comp_zero, ← Category.assoc, totalSummandProjectionAt_other K p q n i j h hij hi, zero_comp]

set_option backward.isDefEq.respectTransparency false in
theorem cochainTotal_horizontal_zero_incoming (q n : ℕ) (h : 0+q=n+1) :
    K.D₁ (ComplexShape.up ℕ) n (n+1) ≫ totalSummandProjectionAt K 0 q (n+1) h = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i+j=n at hij
  rw [← Category.assoc, HomologicalComplex₂.ι_D₁,
    HomologicalComplex₂.d₁_eq K (ComplexShape.up ℕ)
      (show (ComplexShape.up ℕ).Rel i (i+1) from rfl) j (n+1) (by change i+1+j=n+1; omega)]
  simp only [cochainNatTotalHorizontalSign, one_smul, Category.assoc]
  rw [totalSummandProjectionAt_other K 0 q (n+1) (i+1) j h (by omega) (by omega), comp_zero, comp_zero]

end Sharpness
