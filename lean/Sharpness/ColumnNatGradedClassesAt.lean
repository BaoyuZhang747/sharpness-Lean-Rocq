import Sharpness.ColumnNatGradedClasses

/-! Degree-transported versions of the actual graded comparisons.
The degree equation is explicit, so arithmetic rebracketing does not
change cycle representatives or the cohomology comparison. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalColumnNatGradedTermIsoAt (p q n : ℕ) (hn : p+q=n) :
    (totalColumnNatAssociatedGraded K p).X n ≅ (K.X p).X q :=
  eqToIso (congrArg (totalColumnNatAssociatedGraded K p).X hn.symm) ≪≫
    totalColumnNatAssociatedGradedTermIso K p q

def totalColumnNatGradedCohomologyIsoAt (p q n : ℕ) (hn : p+q=n) :
    (totalColumnNatAssociatedGraded K p).homology n ≅ (K.X p).homology q :=
  eqToIso (congrArg (fun m => (totalColumnNatAssociatedGraded K p).homology m) hn.symm) ≪≫
    totalColumnNatGradedCohomologyIso K p q

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnNatGradedCohomologyIso_cycleAt {M : ModuleCat.{u} R} (p q n : ℕ) (hn : p+q=n)
    (x : M ⟶ (totalColumnNatAssociatedGraded K p).X n)
    (hx : x ≫ (totalColumnNatAssociatedGraded K p).d n (n+1) = 0)
    (y : M ⟶ (K.X p).X q) (hy : y ≫ (K.X p).d q (q+1) = 0)
    (hxy : x ≫ (totalColumnNatGradedTermIsoAt K p q n hn).hom = y) :
    ((totalColumnNatAssociatedGraded K p).liftCycles x (n+1) ((ComplexShape.up ℕ).next_eq' rfl) hx ≫
        (totalColumnNatAssociatedGraded K p).homologyπ n) ≫
      (totalColumnNatGradedCohomologyIsoAt K p q n hn).hom =
    (K.X p).liftCycles y (q+1) ((ComplexShape.up ℕ).next_eq' rfl) hy ≫ (K.X p).homologyπ q := by
  subst n
  simpa only [totalColumnNatGradedTermIsoAt, totalColumnNatGradedCohomologyIsoAt,
    eqToIso_refl, Iso.trans_hom, Iso.refl_hom, Category.id_comp, Category.comp_id] using
      (totalColumnNatGradedCohomologyIso_cycle K p q x hx y hy (by
        simpa only [totalColumnNatGradedTermIsoAt, eqToIso_refl, Iso.trans_hom,
          Iso.refl_hom, Category.id_comp] using hxy))

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnSummandLiftAt_quotient_leading (p q n : ℕ) (hn : p+q=n) :
    totalColumnSummandLiftAt K p q n hn ≫
      (cokernel.π (totalColumnFilteredMap K (Nat.le_succ p))).f n ≫
        (totalColumnNatGradedTermIsoAt K p q n hn).hom = 𝟙 _ := by
  subst n
  simp only [totalColumnNatGradedTermIsoAt, eqToIso_refl, Iso.trans_hom,
    Iso.refl_hom, Category.id_comp, totalColumnNatAssociatedGradedTermIso_projection]
  calc
    _ = totalColumnSummandLift K p q ≫ (totalColumnFilteredInclusion K p).f (p+q) ≫
        totalSummandProjection K p q := rfl
    _ = K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl ≫ totalSummandProjection K p q := by
      rw [← Category.assoc, totalColumnSummandLift_inclusion]
    _ = 𝟙 _ := totalSummandProjection_inclusion K p q

theorem totalColumnNatVerticalCycleClass_epi (p q : ℕ) : Epi (totalColumnNatVerticalCycleClass K p q) := by
  apply (epi_comp_iff_of_isIso _ (totalColumnNatGradedCohomologyIso K p q).hom).mp
  rw [totalColumnNatGradedCohomologyIso_cycleClass]
  infer_instance

end Sharpness
