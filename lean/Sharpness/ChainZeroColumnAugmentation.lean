import Sharpness.ChainZeroColumnDifferential

/-! An actual horizontal chain cocone gives a chain map out of the
signed native total. Its degreewise formula is the actual zero-column
projection followed by the given cocone map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    {A : ChainComplex (ModuleCat.{u} R) ℕ} (a : K.X 0 ⟶ A) (ha : K.d 1 0 ≫ a = 0)

include ha in
theorem chainZeroColumnAugmentation_comm (n : ℕ) :
    (chainTotalProjection K 0 (n+1) (n+1) (by omega) ≫ a.f (n+1)) ≫ A.d (n+1) n =
      (K.total (ComplexShape.down ℕ)).d (n+1) n ≫
        (chainTotalProjection K 0 n n (by omega) ≫ a.f n) := by
  calc
    _ = (chainTotalProjection K 0 (n+1) (n+1) (by omega) ≫ (K.X 0).d (n+1) n) ≫ a.f n := by
      rw [Category.assoc, a.comm, ← Category.assoc]
    _ = (K.D₂ (ComplexShape.down ℕ) (n+1) n ≫ chainTotalProjection K 0 n n (by omega)) ≫ a.f n :=
      congrArg (fun t => t ≫ a.f n) (chainZeroColumn_vertical K n).symm
    _ = (K.D₁ (ComplexShape.down ℕ) (n+1) n + K.D₂ (ComplexShape.down ℕ) (n+1) n) ≫
        (chainTotalProjection K 0 n n (by omega) ≫ a.f n) := by
      have hs :
          (K.D₁ (ComplexShape.down ℕ) (n+1) n + K.D₂ (ComplexShape.down ℕ) (n+1) n) ≫
              (chainTotalProjection K 0 n n (by omega) ≫ a.f n) =
            K.D₂ (ComplexShape.down ℕ) (n+1) n ≫
              (chainTotalProjection K 0 n n (by omega) ≫ a.f n) :=
        (Preadditive.add_comp _ _ _ _ _ _).trans
          ((congrArg (fun t => t + K.D₂ (ComplexShape.down ℕ) (n+1) n ≫
              (chainTotalProjection K 0 n n (by omega) ≫ a.f n))
            (chainZeroColumn_horizontal_zero K a ha n)).trans (zero_add _))
      exact (Category.assoc _ _ _).trans hs.symm
    _ = _ := by rw [HomologicalComplex₂.total_d]

def chainZeroColumnAugmentation : K.total (ComplexShape.down ℕ) ⟶ A where
  f n := chainTotalProjection K 0 n n (by omega) ≫ a.f n
  comm' i j hij := by
    have hi : j+1=i := hij
    subst i
    exact chainZeroColumnAugmentation_comm K a ha j

theorem chainZeroColumnAugmentation_f (n : ℕ) :
    (chainZeroColumnAugmentation K a ha).f n = chainTotalProjection K 0 n n (by omega) ≫ a.f n := rfl

end Sharpness
