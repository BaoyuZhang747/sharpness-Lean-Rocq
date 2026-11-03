import Sharpness.ColumnNatGradedComplexIso
import Sharpness.ColumnConnectingClasses
import Sharpness.ExtendCycleClasses
import Sharpness.CochainUnitTwistClasses

/-! The previously constructed associated-graded cohomology isomorphism
sends the actual lifted vertical cycle to its original vertical class. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnNatGradedComplexIso_component (p q : ℕ) :
    (totalColumnNatGradedComplexIso K p).hom.f (p+q) ≫
      ((cochainUnitTwist (K.X p) ((-1 : ℤˣ)^p)).extendXIso (columnNatEmbedding p) rfl).hom =
    (totalColumnNatAssociatedGradedTermIso K p q).hom := by
  change ((columnNatEmbedding p).liftExtend (totalColumnNatGradedRestrictionIso K p).hom
    (strictlySupported_hasLift _ _ _ _)).f (p+q) ≫ _ = _
  have hf := (columnNatEmbedding p).liftExtend_f (totalColumnNatGradedRestrictionIso K p).hom
    (strictlySupported_hasLift _ _ _ _) (i := q) (i' := p+q) (show (columnNatEmbedding p).f q = p+q from rfl)
  calc
    _ = ((totalColumnNatAssociatedGraded K p).restrictionXIso (columnNatEmbedding p) rfl).inv ≫
        (totalColumnNatGradedRestrictionIso K p).hom.f q ≫
          ((cochainUnitTwist (K.X p) ((-1 : ℤˣ)^p)).extendXIso (columnNatEmbedding p) rfl).inv ≫
            ((cochainUnitTwist (K.X p) ((-1 : ℤˣ)^p)).extendXIso (columnNatEmbedding p) rfl).hom := by
      exact (congrArg (fun t => t ≫
        ((cochainUnitTwist (K.X p) ((-1 : ℤˣ)^p)).extendXIso (columnNatEmbedding p) rfl).hom) hf).trans
          (by simp only [Category.assoc])
    _ = _ := by
      simp only [Iso.inv_hom_id, Category.comp_id]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnConnectingQuotientCycle_leading (p q : ℕ) :
    totalColumnConnectingQuotientCycle K p q ≫
      (totalColumnNatAssociatedGradedTermIso K p q).hom = (K.X p).iCycles q := by
  simp only [totalColumnConnectingQuotientCycle, totalColumnConnectingSource, Category.assoc,
    totalColumnNatAssociatedGradedTermIso_projection]
  have h : totalColumnSummandLift K p q ≫ ModuleCat.ofHom (totalColumnLeadingMap K p q) = 𝟙 _ := by
    calc
      _ = totalColumnSummandLift K p q ≫ (totalColumnFilteredInclusion K p).f (p+q) ≫
          totalSummandProjection K p q := rfl
      _ = K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl ≫ totalSummandProjection K p q := by
        rw [← Category.assoc, totalColumnSummandLift_inclusion]
      _ = 𝟙 _ := totalSummandProjection_inclusion K p q
  rw [h, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnNatGradedCohomologyIso_cycle {M : ModuleCat.{u} R} (p q : ℕ)
    (x : M ⟶ (totalColumnNatAssociatedGraded K p).X (p+q))
    (hx : x ≫ (totalColumnNatAssociatedGraded K p).d (p+q) (p+q+1) = 0)
    (y : M ⟶ (K.X p).X q) (hy : y ≫ (K.X p).d q (q+1) = 0)
    (hxy : x ≫ (totalColumnNatAssociatedGradedTermIso K p q).hom = y) :
    ((totalColumnNatAssociatedGraded K p).liftCycles x (p+q+1) ((ComplexShape.up ℕ).next_eq' rfl) hx ≫
        (totalColumnNatAssociatedGraded K p).homologyπ (p+q)) ≫
      (totalColumnNatGradedCohomologyIso K p q).hom =
    (K.X p).liftCycles y (q+1) ((ComplexShape.up ℕ).next_eq' rfl) hy ≫ (K.X p).homologyπ q := by
  let V := K.X p
  let W := cochainUnitTwist V ((-1 : ℤˣ)^p)
  let Q := totalColumnNatAssociatedGraded K p
  have hw : y ≫ W.d q (q+1) = 0 := by
    rw [cochainUnitTwist_d, Linear.comp_units_smul, hy, smul_zero]
  have he : x ≫ (totalColumnNatGradedComplexIso K p).hom.f (p+q) ≫
      (W.extendXIso (columnNatEmbedding p) rfl).hom = y := by
    exact (congrArg (fun t => x ≫ t) (totalColumnNatGradedComplexIso_component K p q)).trans
      hxy
  have hc := extendCycleClass_comparison (columnNatEmbedding p) Q W
    (totalColumnNatGradedComplexIso K p).hom q (q+1) (p+q) (p+q+1) rfl
      ((ComplexShape.up ℕ).next_eq' rfl) ((ComplexShape.up ℕ).next_eq' rfl)
      x hx y hw he
  have ht := cochainUnitTwistCycleClass V ((-1 : ℤˣ)^p) q y hy hw
  calc
    _ = ((Q.liftCycles x (p+q+1) ((ComplexShape.up ℕ).next_eq' rfl) hx ≫ Q.homologyπ (p+q)) ≫
          HomologicalComplex.homologyMap (totalColumnNatGradedComplexIso K p).hom (p+q) ≫
            (W.extendHomologyIso (columnNatEmbedding p) rfl).hom) ≫
              (cochainUnitTwistCycleCohomologyIso V ((-1 : ℤˣ)^p) q).hom := by
      simp only [totalColumnNatGradedCohomologyIso,
        Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map,
        Q, W, V, Category.assoc]
    _ = (W.liftCycles y (q+1) ((ComplexShape.up ℕ).next_eq' rfl) hw ≫ W.homologyπ q) ≫
        (cochainUnitTwistCycleCohomologyIso V ((-1 : ℤˣ)^p) q).hom :=
      congrArg (fun t => t ≫ (cochainUnitTwistCycleCohomologyIso V ((-1 : ℤˣ)^p) q).hom) hc
    _ = _ := ht

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnNatGradedCohomologyIso_cycleClass (p q : ℕ) :
    totalColumnNatVerticalCycleClass K p q ≫ (totalColumnNatGradedCohomologyIso K p q).hom =
      (K.X p).homologyπ q := by
  have hv := (K.X p).iCycles_d q (q+1)
  have hc := totalColumnNatGradedCohomologyIso_cycle K p q
    (totalColumnConnectingQuotientCycle K p q) (totalColumnConnectingQuotientCycle_closed K p q)
    ((K.X p).iCycles q) hv (totalColumnConnectingQuotientCycle_leading K p q)
  have hl : (K.X p).liftCycles ((K.X p).iCycles q) (q+1) ((ComplexShape.up ℕ).next_eq' rfl) hv = 𝟙 _ := by
    apply (cancel_mono ((K.X p).iCycles q)).mp
    simp only [HomologicalComplex.liftCycles_i, Category.id_comp]
  exact hc.trans (by rw [hl, Category.id_comp])

end Sharpness
