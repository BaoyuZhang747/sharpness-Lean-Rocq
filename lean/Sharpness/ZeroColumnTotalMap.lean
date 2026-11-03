import Sharpness.FirstQuadrantFilteredCochains
import Sharpness.TotalSummandProjectionAt

/-! An actual horizontal cocycle of cochain-complex maps into column
zero gives an actual map to the total complex. Its leading projection
is the given map, with no convergence or quasi-isomorphism assumption. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
theorem zeroColumnTotal_d (n : ℕ) :
    K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp) ≫
        (K.total (ComplexShape.up ℕ)).d n (n+1) =
      (K.d 0 1).f n ≫ K.ιTotal (ComplexShape.up ℕ) 1 n (n+1) (by change 1+n=n+1; omega) +
        (K.X 0).d n (n+1) ≫ K.ιTotal (ComplexShape.up ℕ) 0 (n+1) (n+1) (by simp) := by
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.up ℕ).Rel 0 1 from rfl) n
      (n+1) (by change 1+n=n+1; omega),
    HomologicalComplex₂.d₂_eq _ _ 0 (show (ComplexShape.up ℕ).Rel n (n+1) from rfl)
      (n+1) (by change 0+(n+1)=n+1; omega)]
  simp only [cochainNatTotalHorizontalSign, cochainNatTotalVerticalSign, pow_zero, one_smul]

variable {A : CochainComplex (ModuleCat.{u} R) ℕ} (a : A ⟶ K.X 0) (ha : a ≫ K.d 0 1=0)

set_option backward.isDefEq.respectTransparency false in
def zeroColumnTotalMap : A ⟶ K.total (ComplexShape.up ℕ) :=
  CochainComplex.ofHom (fun n => a.f n ≫ K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp)) (by
    intro n
    have hh : a.f n ≫ (K.d 0 1).f n=0 := by
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
        HomologicalComplex.congr_hom ha n
    rw [Category.assoc, zeroColumnTotal_d, Preadditive.comp_add]
    simp only [← Category.assoc, hh, zero_comp, zero_add]
    rw [a.comm])

set_option backward.isDefEq.respectTransparency false in
theorem zeroColumnTotalMap_projection (n : ℕ) :
    (zeroColumnTotalMap K a ha).f n ≫ totalSummandProjectionAt K 0 n n (by omega) = a.f n := by
  change (a.f n ≫ K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp)) ≫ _ = _
  have h : K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp) ≫
      totalSummandProjectionAt K 0 n n (by omega) = 𝟙 _ :=
    totalSummandProjectionAt_inclusion K 0 n n (by omega)
  exact (Category.assoc _ _ _).trans ((congrArg (fun t => a.f n ≫ t) h).trans (Category.comp_id _))

end Sharpness
