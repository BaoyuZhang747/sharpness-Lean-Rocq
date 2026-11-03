import Sharpness.DualNatBicomplex

/-! The two actual chain-total differential components on a summand,
including the absent horizontal/vertical arrows at the zero boundary. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))

set_option backward.isDefEq.respectTransparency false in
theorem chainTotal_horizontal_outgoing (p q n : ℕ) (h : p+q=n) :
    K.ιTotal (ComplexShape.down ℕ) (p+1) q (n+1) (by change p+1+q=n+1; omega) ≫ K.D₁ (ComplexShape.down ℕ) (n+1) n =
      (K.d (p+1) p).f q ≫ K.ιTotal (ComplexShape.down ℕ) p q n h := by
  rw [HomologicalComplex₂.ι_D₁, HomologicalComplex₂.d₁_eq K (ComplexShape.down ℕ)
    (show (ComplexShape.down ℕ).Rel (p+1) p from rfl) q n h]
  change (1 : ℤˣ) • _ = _
  exact one_smul _ _

set_option backward.isDefEq.respectTransparency false in
theorem chainTotal_horizontal_zero_outgoing (q n : ℕ) (h : 0+q=n+1) :
    K.ιTotal (ComplexShape.down ℕ) 0 q (n+1) h ≫ K.D₁ (ComplexShape.down ℕ) (n+1) n = 0 := by
  rw [HomologicalComplex₂.ι_D₁]
  apply HomologicalComplex₂.d₁_eq_zero
  change ¬ (ComplexShape.down ℕ).next 0 + 1 = (0 : ℕ)
  omega

set_option backward.isDefEq.respectTransparency false in
theorem chainTotal_vertical_outgoing (p q n : ℕ) (h : p+q=n) :
    K.ιTotal (ComplexShape.down ℕ) p (q+1) (n+1) (by change p+(q+1)=n+1; omega) ≫ K.D₂ (ComplexShape.down ℕ) (n+1) n =
      (-1 : ℤˣ)^p • ((K.X p).d (q+1) q ≫ K.ιTotal (ComplexShape.down ℕ) p q n h) := by
  rw [HomologicalComplex₂.ι_D₂, HomologicalComplex₂.d₂_eq K (ComplexShape.down ℕ) p
    (show (ComplexShape.down ℕ).Rel (q+1) q from rfl) n h]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem chainTotal_vertical_zero_outgoing (p n : ℕ) (h : p+0=n+1) :
    K.ιTotal (ComplexShape.down ℕ) p 0 (n+1) h ≫ K.D₂ (ComplexShape.down ℕ) (n+1) n = 0 := by
  rw [HomologicalComplex₂.ι_D₂]
  apply HomologicalComplex₂.d₂_eq_zero
  change ¬ (ComplexShape.down ℕ).next 0 + 1 = (0 : ℕ)
  omega

end Sharpness
