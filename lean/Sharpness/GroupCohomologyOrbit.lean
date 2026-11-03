import Sharpness.GroupCohomologyTransferInput

/-! Actual descent of native ordinary cohomology to the fusion orbit
category. Target-inner invariance of both variances is deduced using
native functoriality and the general published transfer identities. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S R : Type u} [Group S] [Finite S] [CommRing R] (F : FusionSystem S)
    {A : Type u} [AddCommGroup A] [Module R A]
    {n : ℕ} (I : F.GroupCohomologyTransferLaws (R := R) A n)

include I

theorem groupCohomologyRawPush_id (P : F.Object) :
    F.groupCohomologyRawPush I.transfer (𝟙 P) = LinearMap.id :=
  (I.transfer_iso (Iso.refl P)).trans (F.groupCohomologyRawPull_id P n)

theorem groupCohomologyRawPush_inner (P : F.Object) (r : P.subgroup) :
    F.groupCohomologyRawPush I.transfer (F.inner P r) = LinearMap.id := by
  let e := F.isoOfEqualOrder (F.inner P r) rfl
  have hi : F.groupCohomologyRawPull (R := R) (A := A) e.hom n = LinearMap.id := I.inner P r
  have hinv := congrArg (fun f => F.groupCohomologyRawPull (R := R) (A := A) f n) e.hom_inv_id
  rw [F.groupCohomologyRawPull_comp, hi, LinearMap.id_comp,
    F.groupCohomologyRawPull_id] at hinv
  exact (I.transfer_iso e).trans hinv

theorem groupCohomologyRawPull_same_orbit {P Q : F.Object} (f g : P ⟶ Q)
    (same : F.toOrbit.map f = F.toOrbit.map g) :
    F.groupCohomologyRawPull (R := R) (A := A) f n = F.groupCohomologyRawPull g n := by
  obtain ⟨r, hr⟩ := (F.orbit_map_eq_iff f g).mp same
  have hg : g = f ≫ F.inner Q r := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    exact hr x
  rw [hg, F.groupCohomologyRawPull_comp, I.inner, LinearMap.comp_id]

theorem groupCohomologyRawPush_same_orbit {P Q : F.Object} (f g : P ⟶ Q)
    (same : F.toOrbit.map f = F.toOrbit.map g) :
    F.groupCohomologyRawPush I.transfer f = F.groupCohomologyRawPush I.transfer g := by
  obtain ⟨r, hr⟩ := (F.orbit_map_eq_iff f g).mp same
  have hg : g = f ≫ F.inner Q r := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    exact hr x
  rw [hg, I.transfer_comp, F.groupCohomologyRawPush_inner I, LinearMap.id_comp]

def groupCohomologyOrbitPull {P Q : F.Orbit} (f : P ⟶ Q) :
    OrdinaryCohomology.value R Q.as.subgroup A n →ₗ[R]
      OrdinaryCohomology.value R P.as.subgroup A n :=
  F.groupCohomologyRawPull (F.orbitRepresentative f) n

def groupCohomologyOrbitPush {P Q : F.Orbit} (f : P ⟶ Q) :
    OrdinaryCohomology.value R P.as.subgroup A n →ₗ[R]
      OrdinaryCohomology.value R Q.as.subgroup A n :=
  F.groupCohomologyRawPush I.transfer (F.orbitRepresentative f)

theorem groupCohomologyOrbitPull_raw {P Q : F.Object} (f : P ⟶ Q) :
    F.groupCohomologyOrbitPull (R := R) (A := A) (n := n) (F.toOrbit.map f) =
      F.groupCohomologyRawPull f n :=
  F.groupCohomologyRawPull_same_orbit I _ _ (F.orbitRepresentative_map _)

theorem groupCohomologyOrbitPush_raw {P Q : F.Object} (f : P ⟶ Q) :
    F.groupCohomologyOrbitPush I (F.toOrbit.map f) = F.groupCohomologyRawPush I.transfer f :=
  F.groupCohomologyRawPush_same_orbit I _ _ (F.orbitRepresentative_map _)

end Sharpness.FusionSystem
