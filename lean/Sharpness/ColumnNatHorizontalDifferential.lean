import Sharpness.ColumnNatGradedClassesAt
import Sharpness.CochainCycleClassMap

/-! The actual natural-number adjacent-quotient connecting differential
is the actual horizontal cohomology map under the already constructed
graded cohomology comparison. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnNatCokernelDifferential_horizontal (p q : ℕ) :
    totalColumnNatCokernelDifferential K p q ≫
      (totalColumnNatGradedCohomologyIsoAt K (p+1) q (p+q+1) (by omega)).hom =
    (totalColumnNatGradedCohomologyIso K p q).hom ≫
      HomologicalComplex.homologyMap (K.d p (p+1)) q := by
  let V := K.X p
  let W := K.X (p+1)
  let F := totalColumnFilteredComplex K (p+1)
  let Q := totalColumnNatAssociatedGraded K (p+1)
  let π := cokernel.π (totalColumnFilteredMap K (Nat.le_succ (p+1)))
  let x := totalColumnConnectingTarget K p q
  have hx : x ≫ F.d (p+q+1) (p+q+1+1) = 0 := totalColumnConnectingTarget_closed K p q
  let z := x ≫ π.f (p+q+1)
  have hz : z ≫ Q.d (p+q+1) (p+q+1+1) = 0 :=
    cochainCycle_map_closed π (p+q+1) (p+q+1+1) x hx
  let y := V.iCycles q ≫ (K.d p (p+1)).f q
  have hy : y ≫ W.d q (q+1) = 0 := by
    dsimp only [y]
    rw [Category.assoc, (K.d p (p+1)).comm, ← Category.assoc,
      HomologicalComplex.iCycles_d, zero_comp]
  have hzy : z ≫ (totalColumnNatGradedTermIsoAt K (p+1) q (p+q+1) (by omega)).hom = y := by
    simp only [z, x, y, totalColumnConnectingTarget, Category.assoc,
      totalColumnSummandLiftAt_quotient_leading, Category.comp_id, V, π]
  have hc := totalColumnNatGradedCohomologyIso_cycleAt K (p+1) q (p+q+1) (by omega) z hz y hy hzy
  have hm := cochainCycleClass_map π (p+q+1) (p+q+1+1) ((ComplexShape.up ℕ).next_eq' rfl) x hx
  have hcycles : W.liftCycles y (q+1) ((ComplexShape.up ℕ).next_eq' rfl) hy =
      HomologicalComplex.cyclesMap (K.d p (p+1)) q := by
    apply (cancel_mono (W.iCycles q)).mp
    simp only [HomologicalComplex.liftCycles_i]
    exact (HomologicalComplex.cyclesMap_i (K.d p (p+1)) q).symm
  letI := totalColumnNatVerticalCycleClass_epi K p q
  apply (cancel_epi (totalColumnNatVerticalCycleClass K p q)).mp
  calc
    _ = ((F.liftCycles x (p+q+1+1) ((ComplexShape.up ℕ).next_eq' rfl) hx ≫ F.homologyπ (p+q+1)) ≫
        HomologicalComplex.homologyMap π (p+q+1)) ≫
          (totalColumnNatGradedCohomologyIsoAt K (p+1) q (p+q+1) (by omega)).hom := by
      rw [← Category.assoc, totalColumnNatVerticalCycleClass_d]
      simp only [F, x, π, Category.assoc]
    _ = (Q.liftCycles z (p+q+1+1) ((ComplexShape.up ℕ).next_eq' rfl) hz ≫ Q.homologyπ (p+q+1)) ≫
        (totalColumnNatGradedCohomologyIsoAt K (p+1) q (p+q+1) (by omega)).hom :=
      congrArg (fun t => t ≫ (totalColumnNatGradedCohomologyIsoAt K (p+1) q (p+q+1) (by omega)).hom) hm
    _ = W.liftCycles y (q+1) ((ComplexShape.up ℕ).next_eq' rfl) hy ≫ W.homologyπ q := hc
    _ = V.homologyπ q ≫ HomologicalComplex.homologyMap (K.d p (p+1)) q := by
      rw [hcycles]
      exact (HomologicalComplex.homologyπ_naturality (K.d p (p+1)) q).symm
    _ = _ := by
      rw [← totalColumnNatGradedCohomologyIso_cycleClass K p q, Category.assoc]

end Sharpness
