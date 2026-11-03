import Sharpness.ZeroColumnTotalProjection

/-! The vertical total differential has one incoming contribution
to a positive row with the actual (-1)^p sign, and none to row zero. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
theorem cochainTotal_vertical_incoming (p q n : ℕ) (h : p+q=n) :
    K.D₂ (ComplexShape.up ℕ) n (n+1) ≫
        totalSummandProjectionAt K p (q+1) (n+1) (by omega) =
      (-1 : ℤˣ)^p • (totalSummandProjectionAt K p q n h ≫ (K.X p).d q (q+1)) := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i+j=n at hij
  have hd : K.ιTotal (ComplexShape.up ℕ) i j n hij ≫ K.D₂ (ComplexShape.up ℕ) n (n+1) =
      (-1 : ℤˣ)^i • ((K.X i).d j (j+1) ≫ K.ιTotal (ComplexShape.up ℕ) i (j+1) (n+1) (by change i+(j+1)=n+1; omega)) := by
    rw [HomologicalComplex₂.ι_D₂, HomologicalComplex₂.d₂_eq K (ComplexShape.up ℕ) i
      (show (ComplexShape.up ℕ).Rel j (j+1) from rfl) (n+1) (by change i+(j+1)=n+1; omega)]
    rfl
  rw [← Category.assoc, hd, Linear.units_smul_comp, Category.assoc, Linear.comp_units_smul]
  by_cases hi : i=p
  · subst i
    have hj : j=q := by omega
    subst j
    rw [totalSummandProjectionAt_inclusion, Category.comp_id, ← Category.assoc,
      totalSummandProjectionAt_inclusion, Category.id_comp]
  · rw [totalSummandProjectionAt_other K p (q+1) (n+1) i (j+1) (by omega) (by omega) hi,
      comp_zero, smul_zero, ← Category.assoc, totalSummandProjectionAt_other K p q n i j h hij hi,
      zero_comp, smul_zero]

set_option backward.isDefEq.respectTransparency false in
theorem cochainTotal_vertical_zero_incoming (p n : ℕ) (h : p+0=n+1) :
    K.D₂ (ComplexShape.up ℕ) n (n+1) ≫ totalSummandProjectionAt K p 0 (n+1) h = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i+j=n at hij
  rw [← Category.assoc, HomologicalComplex₂.ι_D₂,
    HomologicalComplex₂.d₂_eq K (ComplexShape.up ℕ) i
      (show (ComplexShape.up ℕ).Rel j (j+1) from rfl) (n+1) (by change i+(j+1)=n+1; omega)]
  simp only [cochainNatTotalVerticalSign, Linear.units_smul_comp, Category.assoc]
  rw [totalSummandProjectionAt_other K p 0 (n+1) i (j+1) h (by omega) (by omega),
    comp_zero, smul_zero, comp_zero]

end Sharpness
