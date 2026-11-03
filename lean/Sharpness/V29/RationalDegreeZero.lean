import Sharpness.Manuscript.CohomologyUnconditional
import Sharpness.Unconditional.GroupCohomologyTransferUnit
import Sharpness.Unconditional.MinimalSupport

/-! Native ordinary degree-zero cohomology with rational coefficients.
The coordinates below identify actual pullbacks and actual inverse-Shapiro
transfers, rather than assigning new maps to an abstract constant functor. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory

variable {R G H A : Type u} [CommRing R] [Group G] [Group H]
  [AddCommGroup A] [Module R A]

def degreeZeroIso (R G A : Type u) [CommRing R] [Group G]
    [AddCommGroup A] [Module R A] : value R G A 0 ≅ ModuleCat.of R A :=
  groupCohomology.H0IsoOfIsTrivial (Rep.trivial R G A)

theorem degreeZero_pull (f : G →* H) :
    pull (R := R) (A := A) f 0 ≫ (degreeZeroIso R G A).hom =
      (degreeZeroIso R H A).hom := by
  have h := groupCohomology.map_H0Iso_hom_f f
    (trivialRestrictionHom (R := R) (A := A) f)
  change pull f 0 ≫ (degreeZeroIso R G A).hom =
    (degreeZeroIso R H A).hom ≫ 𝟙 (ModuleCat.of R A) at h
  simpa using h

theorem degreeZero_pull_apply (f : G →* H) (x : value R H A 0) :
    (degreeZeroIso R G A).hom (pull f 0 x) = (degreeZeroIso R H A).hom x :=
  congrArg (fun m => m x) (degreeZero_pull (R := R) (A := A) f)

theorem degreeZero_transfer (K : Subgroup G) [K.FiniteIndex]
    (x : value R K A 0) :
    (degreeZeroIso R G A).hom (transfer K 0 x) =
      K.index • (degreeZeroIso R K A).hom x := by
  let y := (degreeZeroIso R G A).inv ((degreeZeroIso R K A).hom x)
  have hy : pull K.subtype 0 y = x := by
    apply (degreeZeroIso R K A).toLinearEquiv.injective
    change (degreeZeroIso R K A).hom (pull K.subtype 0 y) =
      (degreeZeroIso R K A).hom x
    rw [degreeZero_pull_apply]
    exact Iso.inv_hom_id_apply _ _
  rw [← hy]
  have h := congrArg (fun m => m y) (pull_transfer (R := R) (A := A) K 0)
  change transfer K 0 (pull K.subtype 0 y) = K.index • y at h
  rw [h, map_nsmul, degreeZero_pull_apply]

theorem degreeZero_subgroupTransfer [Finite G] (P Q : Subgroup G) (h : P ≤ Q)
    (x : value R P A 0) :
    (degreeZeroIso R Q A).hom (subgroupTransfer P Q h 0 x) =
      (P.subgroupOf Q).index • (degreeZeroIso R P A).hom x := by
  change (degreeZeroIso R Q A).hom
    (transfer (P.subgroupOf Q) 0
      (pull (Subgroup.subgroupOfEquivOfLe h).toMonoidHom 0 x)) = _
  rw [degreeZero_transfer, degreeZero_pull_apply]

end Sharpness.OrdinaryCohomology

namespace Sharpness.FusionSystem
open CategoryTheory OrdinaryCohomology
variable {S : Type} [Group S] [Finite S] (F : FusionSystem S)

/-- The counterexample uses the existing full native cohomology Mackey functor. -/
abbrev rationalDegreeZeroMackey :=
  F.nativeGroupCohomologyMackey (R := ℚ) (A := ℚ) 0

def rationalDegreeZeroCoordinate (P : F.Orbit) :
    (F.rationalDegreeZeroMackey).Value P ≃ₗ[ℚ] ℚ :=
  (degreeZeroIso ℚ P.as.subgroup ℚ).toLinearEquiv

theorem rationalDegreeZero_pull {P Q : F.Object} (f : P ⟶ Q)
    (x : (F.rationalDegreeZeroMackey).Value (F.toOrbit.obj Q)) :
    F.rationalDegreeZeroCoordinate (F.toOrbit.obj P)
      ((F.rationalDegreeZeroMackey).pull (F.toOrbit.map f) x) =
      F.rationalDegreeZeroCoordinate (F.toOrbit.obj Q) x := by
  change (degreeZeroIso ℚ P.subgroup ℚ).hom
    ((F.groupCohomologyMackey (F.cohomologyTransferLaws 0)).pull (F.toOrbit.map f) x) = _
  rw [F.groupCohomologyMackey_pull_raw]
  exact degreeZero_pull_apply f.val x

theorem rationalDegreeZero_push {P Q : F.Object} (f : P ⟶ Q)
    (x : (F.rationalDegreeZeroMackey).Value (F.toOrbit.obj P)) :
    F.rationalDegreeZeroCoordinate (F.toOrbit.obj Q)
      ((F.rationalDegreeZeroMackey).push (F.toOrbit.map f) x) =
      ((F.imageSubgroup f).subgroupOf Q.subgroup).index •
        F.rationalDegreeZeroCoordinate (F.toOrbit.obj P) x := by
  change (degreeZeroIso ℚ Q.subgroup ℚ).hom
    ((F.groupCohomologyMackey (F.cohomologyTransferLaws 0)).push (F.toOrbit.map f) x) = _
  rw [F.groupCohomologyMackey_push_raw]
  change (degreeZeroIso ℚ Q.subgroup ℚ).hom
    (subgroupTransfer (F.imageSubgroup f) Q.subgroup (F.image_le f) 0
      (pull (F.imageIso f).inv.val 0 x)) = _
  rw [degreeZero_subgroupTransfer, degreeZero_pull_apply]
  rfl

theorem rationalDegreeZero_nonzero (P : F.Orbit) :
    ∃ x : F.rationalDegreeZeroMackey.Value P, x ≠ 0 := by
  refine ⟨(F.rationalDegreeZeroCoordinate P).symm 1, ?_⟩
  intro h
  have e := congrArg (F.rationalDegreeZeroCoordinate P) h
  simpa using e

theorem rationalDegreeZero_transfer {P Q : Subgroup S} (h : P ≤ Q)
    (x : F.rationalDegreeZeroMackey.Value (F.toOrbit.obj ⟨P⟩)) :
    F.rationalDegreeZeroCoordinate (F.toOrbit.obj ⟨Q⟩)
      (F.rationalDegreeZeroMackey.push (F.toOrbit.map (F.inclusion h)) x) =
      (P.subgroupOf Q).index • F.rationalDegreeZeroCoordinate (F.toOrbit.obj ⟨P⟩) x := by
  rw [F.rationalDegreeZero_push, F.imageSubgroup_inclusion]

theorem rationalDegreeZero_conjugation {P Q : F.Object} (e : P ≅ Q)
    (x : F.rationalDegreeZeroMackey.Value (F.toOrbit.obj P)) :
    F.rationalDegreeZeroCoordinate (F.toOrbit.obj Q)
      (F.rationalDegreeZeroMackey.push (F.toOrbit.map e.hom) x) =
      F.rationalDegreeZeroCoordinate (F.toOrbit.obj P) x := by
  change (degreeZeroIso ℚ Q.subgroup ℚ).hom
    ((F.groupCohomologyMackey (F.cohomologyTransferLaws 0)).push
      (F.toOrbit.map e.hom) x) = _
  rw [F.groupCohomologyMackey_push_raw]
  change (degreeZeroIso ℚ Q.subgroup ℚ).hom
    (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer 0) e.hom x) = _
  rw [F.nativeGroupCohomologyRawPush_iso e 0]
  exact degreeZero_pull_apply e.inv.val x

/-- Simplicity is for Mackey subfunctors, and uses the actual transfer maps. -/
theorem rationalDegreeZero_simple : F.rationalDegreeZeroMackey.IsSimple := by
  classical
  refine ⟨⟨F.toOrbit.obj ⟨⊥⟩, F.rationalDegreeZero_nonzero _⟩, ?_⟩
  intro N
  by_cases hz : ∀ P, N.obj P = ⊥
  · exact Or.inl hz
  · right
    push_neg at hz
    obtain ⟨P, hP⟩ := hz
    have he : ∃ x ∈ N.obj P, x ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hP
      apply le_antisymm _ bot_le
      intro a ha
      exact hn a ha
    obtain ⟨x, hx, hne⟩ := he
    let O : F.Object := ⟨⊥⟩
    let f : O ⟶ P.as := F.inclusion bot_le
    let y := F.rationalDegreeZeroMackey.pull (F.toOrbit.map f) x
    have hy : y ∈ N.obj (F.toOrbit.obj O) := N.pull_closed _ hx
    have ey : F.rationalDegreeZeroCoordinate (F.toOrbit.obj O) y ≠ 0 := by
      rw [rationalDegreeZero_pull]
      intro h
      apply hne
      apply (F.rationalDegreeZeroCoordinate P).injective
      change F.rationalDegreeZeroCoordinate (F.toOrbit.obj P.as) x =
        F.rationalDegreeZeroCoordinate (F.toOrbit.obj P.as) 0
      simpa only [map_zero] using h
    intro Q
    let g : O ⟶ Q.as := F.inclusion bot_le
    let z := F.rationalDegreeZeroMackey.push (F.toOrbit.map g) y
    have hz : z ∈ N.obj Q := N.push_closed _ hy
    have ez : F.rationalDegreeZeroCoordinate Q z ≠ 0 := by
      change F.rationalDegreeZeroCoordinate (F.toOrbit.obj Q.as)
        (F.rationalDegreeZeroMackey.push (F.toOrbit.map g) y) ≠ 0
      rw [rationalDegreeZero_push, nsmul_eq_mul]
      apply mul_ne_zero _ ey
      exact_mod_cast ((F.imageSubgroup g).subgroupOf Q.as.subgroup).index_ne_zero_of_finite
    apply top_unique
    intro v _
    have hv := (N.obj Q).smul_mem
      (F.rationalDegreeZeroCoordinate Q v / F.rationalDegreeZeroCoordinate Q z) hz
    convert hv using 1
    apply (F.rationalDegreeZeroCoordinate Q).injective
    simp only [map_smul, smul_eq_mul]
    field_simp

theorem rationalDegreeZero_minimal_iff (P : Subgroup S) :
    F.IsMinimalSupport F.rationalDegreeZeroMackey P ↔ P = ⊥ := by
  constructor
  · intro h
    by_contra hp
    obtain ⟨x, hx⟩ := F.rationalDegreeZero_nonzero (F.toOrbit.obj ⟨⊥⟩)
    exact hx (h.2 ⊥ (bot_lt_iff_ne_bot.mpr hp) x)
  · rintro rfl
    exact ⟨F.rationalDegreeZero_nonzero _, fun L h => (not_lt_bot h).elim⟩

theorem rationalDegreeZero_centralizer_counterexample [Nontrivial S] :
    F.rationalDegreeZeroMackey.IsSimple ∧
    (∃ x : F.rationalDegreeZeroMackey.Value (F.toOrbit.obj ⟨⊤⟩), x ≠ 0) ∧
    ¬ ∃ L : Subgroup S,
      F.IsMinimalSupport F.rationalDegreeZeroMackey L ∧
        Subgroup.centralizer (L : Set S) ≤ L := by
  refine ⟨F.rationalDegreeZero_simple, F.rationalDegreeZero_nonzero _, ?_⟩
  rintro ⟨L, hL, hc⟩
  have he := (F.rationalDegreeZero_minimal_iff L).mp hL
  subst L
  have ht : (⊤ : Subgroup S) ≤ ⊥ := by
    intro x _
    apply hc
    intro y hy
    have hy' : y = 1 := hy
    simp [hy']
  exact top_ne_bot (le_antisymm ht bot_le)

end Sharpness.FusionSystem
