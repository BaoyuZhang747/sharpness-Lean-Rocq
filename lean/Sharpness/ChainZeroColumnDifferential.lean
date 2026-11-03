import Sharpness.ChainTotalProjection
import Sharpness.ChainTotalOutgoing

/-! The incoming total differential at horizontal degree zero.
The horizontal part is killed only after composing with an actual
cocone map; the vertical part retains its actual native sign. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))

theorem chainZeroColumn_vertical (n : ℕ) :
    K.D₂ (ComplexShape.down ℕ) (n+1) n ≫ chainTotalProjection K 0 n n (by omega) =
      chainTotalProjection K 0 (n+1) (n+1) (by omega) ≫ (K.X 0).d (n+1) n := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  change i+j=n+1 at h
  by_cases hi : i=0
  · subst i
    have hj : j=n+1 := by omega
    subst j
    calc
      _ = ((-1 : ℤˣ)^0 • ((K.X 0).d (n+1) n ≫
          K.ιTotal (ComplexShape.down ℕ) 0 n n (by change 0+n=n; omega))) ≫
          chainTotalProjection K 0 n n (by omega) := by
        rw [← Category.assoc, chainTotal_vertical_outgoing K 0 n n (by omega)]
      _ = (K.X 0).d (n+1) n := by
        rw [pow_zero, one_smul, Category.assoc, chainTotalProjection_inclusion, Category.comp_id]
      _ = (K.ιTotal (ComplexShape.down ℕ) 0 (n+1) (n+1) (by change 0+(n+1)=n+1; omega) ≫
          chainTotalProjection K 0 (n+1) (n+1) (by omega)) ≫ (K.X 0).d (n+1) n := by
        rw [chainTotalProjection_inclusion, Category.id_comp]
      _ = _ := Category.assoc _ _ _
  · cases j with
    | zero =>
      calc
        _ = 0 := by
          rw [← Category.assoc, chainTotal_vertical_zero_outgoing K i n h, zero_comp]
        _ = (K.ιTotal (ComplexShape.down ℕ) i 0 (n+1) h ≫
            chainTotalProjection K 0 (n+1) (n+1) (by omega)) ≫ (K.X 0).d (n+1) n := by
          rw [chainTotalProjection_other K 0 (n+1) (n+1) i 0 (by omega) h hi, zero_comp]
        _ = _ := Category.assoc _ _ _
    | succ q =>
      have hiq : i+q=n := by omega
      calc
        _ = ((-1 : ℤˣ)^i • ((K.X i).d (q+1) q ≫
            K.ιTotal (ComplexShape.down ℕ) i q n hiq)) ≫
            chainTotalProjection K 0 n n (by omega) := by
          rw [← Category.assoc, chainTotal_vertical_outgoing K i q n hiq]
        _ = 0 := by
          rw [Linear.units_smul_comp, Category.assoc,
            chainTotalProjection_other K 0 n n i q (by omega) hiq hi, comp_zero, smul_zero]
        _ = (K.ιTotal (ComplexShape.down ℕ) i (q+1) (n+1) h ≫
            chainTotalProjection K 0 (n+1) (n+1) (by omega)) ≫ (K.X 0).d (n+1) n := by
          rw [chainTotalProjection_other K 0 (n+1) (n+1) i (q+1) (by omega) h hi, zero_comp]
        _ = _ := Category.assoc _ _ _

variable {A : ChainComplex (ModuleCat.{u} R) ℕ} (a : K.X 0 ⟶ A) (ha : K.d 1 0 ≫ a = 0)

include ha in
theorem chainZeroColumn_horizontal_zero (n : ℕ) :
    K.D₁ (ComplexShape.down ℕ) (n+1) n ≫ chainTotalProjection K 0 n n (by omega) ≫ a.f n = 0 := by
  have hh : (K.d 1 0).f n ≫ a.f n = 0 := HomologicalComplex.congr_hom ha n
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  change i+j=n+1 at h
  rw [comp_zero]
  cases i with
  | zero =>
    rw [← Category.assoc, ← Category.assoc, chainTotal_horizontal_zero_outgoing K j n h,
      zero_comp, zero_comp]
  | succ p =>
    have hpj : p+j=n := by omega
    calc
      _ = (K.d (p+1) p).f j ≫
          (K.ιTotal (ComplexShape.down ℕ) p j n hpj ≫
            chainTotalProjection K 0 n n (by omega)) ≫ a.f n := by
        rw [← Category.assoc, chainTotal_horizontal_outgoing K p j n hpj]
        simp only [Category.assoc]
      _ = 0 := by
        cases p with
        | zero =>
          have hj : j=n := by omega
          subst j
          rw [chainTotalProjection_inclusion, Category.id_comp]
          exact hh
        | succ p =>
          rw [chainTotalProjection_other K 0 n n (p+1) j (by omega) hpj (by omega),
            zero_comp, comp_zero]

end Sharpness
