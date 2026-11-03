import Sharpness.CochainUnitTwist

/-! A second cohomology comparison for a unit twist fixes the middle
cochain in each homology short complex. Unlike the degree-dependent
cochain isomorphism, this comparison preserves cycle representatives,
which is the identification needed to compute the first-page map. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R] (V : CochainComplex (ModuleCat.{u} R) ℕ) (a : ℤˣ)

theorem cochainUnitTwist_d_all (i j : ℕ) :
    (cochainUnitTwist V a).d i j = a • V.d i j := by
  by_cases h : i+1 = j
  · subst j
    exact cochainUnitTwist_d V a i
  · rw [(cochainUnitTwist V a).shape i j h, V.shape i j h, smul_zero]
    rfl

set_option backward.isDefEq.respectTransparency false in
def cochainUnitTwistShortComplexIso (n : ℕ) :
    (cochainUnitTwist V a).sc n ≅ V.sc n :=
  ShortComplex.isoMk
    (a • Iso.refl (V.X ((ComplexShape.up ℕ).prev n)))
    (Iso.refl (V.X n))
    (a⁻¹ • Iso.refl (V.X ((ComplexShape.up ℕ).next n)))
    (by
      symm
      change (cochainUnitTwist V a).d ((ComplexShape.up ℕ).prev n) n ≫ 𝟙 _ =
        ((a : ℤ) • 𝟙 _) ≫ V.d ((ComplexShape.up ℕ).prev n) n
      rw [cochainUnitTwist_d_all]
      change ((a : ℤ) • V.d ((ComplexShape.up ℕ).prev n) n) ≫ 𝟙 _ =
        ((a : ℤ) • 𝟙 _) ≫ V.d ((ComplexShape.up ℕ).prev n) n
      simp only [Category.comp_id, Preadditive.zsmul_comp, Category.id_comp])
    (by
      symm
      change (cochainUnitTwist V a).d n ((ComplexShape.up ℕ).next n) ≫
        (((a⁻¹ : ℤˣ) : ℤ) • 𝟙 _) = 𝟙 _ ≫ V.d n ((ComplexShape.up ℕ).next n)
      rw [cochainUnitTwist_d_all]
      change ((a : ℤ) • V.d n ((ComplexShape.up ℕ).next n)) ≫
        (((a⁻¹ : ℤˣ) : ℤ) • 𝟙 _) = _
      simp only [Preadditive.comp_zsmul, Category.comp_id, Category.id_comp,
        smul_smul, ← Units.val_mul]
      simp)

def cochainUnitTwistCycleCohomologyIso (n : ℕ) :
    (cochainUnitTwist V a).homology n ≅ V.homology n :=
  ShortComplex.homologyMapIso (cochainUnitTwistShortComplexIso V a n)

theorem cochainUnitTwistShortComplexIso_middle (n : ℕ) :
    (cochainUnitTwistShortComplexIso V a n).hom.τ₂ = 𝟙 (V.X n) := rfl

end Sharpness
