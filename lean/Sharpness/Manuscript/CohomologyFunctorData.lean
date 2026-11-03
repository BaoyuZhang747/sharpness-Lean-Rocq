import Sharpness.Manuscript.CohomologyCoefficient
import Sharpness.Unconditional.FusionCohomologyPush

/-! Assembly of the native pullbacks and transfers before the Mackey formula.
The only intermediate premise is functoriality of the actual raw push maps.
It is kept separate from the double-coset identity to avoid circularity when
reducing that identity from arbitrary fusion maps to subgroup inclusions. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S R A : Type u} [Group S] [Finite S] [CommRing R]
    [AddCommGroup A] [Module R A] (F : FusionSystem S) (n : ℕ)

theorem nativeCohomologyRawPush_id (P : F.Object) :
    F.groupCohomologyRawPush
      (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n) (𝟙 P) =
      LinearMap.id :=
  (F.nativeGroupCohomologyRawPush_iso (Iso.refl P) n).trans
    (F.groupCohomologyRawPull_id P n)

theorem nativeCohomologyRawPush_inner (P : F.Object) (r : P.subgroup) :
    F.groupCohomologyRawPush
      (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n)
      (F.inner P r) = LinearMap.id := by
  let e := F.isoOfEqualOrder (F.inner P r) rfl
  have hi : F.groupCohomologyRawPull (R := R) (A := A) e.hom n = LinearMap.id :=
    F.cohomologyRawPull_inner_unconditional n P r
  have hinv := congrArg (fun f => F.groupCohomologyRawPull (R := R) (A := A) f n)
    e.hom_inv_id
  rw [F.groupCohomologyRawPull_comp, hi, LinearMap.id_comp,
    F.groupCohomologyRawPull_id] at hinv
  exact (F.nativeGroupCohomologyRawPush_iso e n).trans hinv

def nativeCohomologyOrbitPush {P Q : F.Orbit} (f : P ⟶ Q) :
    OrdinaryCohomology.value R P.as.subgroup A n →ₗ[R]
      OrdinaryCohomology.value R Q.as.subgroup A n :=
  F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) (F.orbitRepresentative f)

variable (hcomp : ∀ {P Q T : F.Object} (f : P ⟶ Q) (g : Q ⟶ T),
  F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (A := A) n) (f ≫ g) =
    (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) g).comp
      (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) f))

include hcomp

theorem nativeCohomologyRawPush_same_orbit {P Q : F.Object} (f g : P ⟶ Q)
    (same : F.toOrbit.map f = F.toOrbit.map g) :
    F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (A := A) n) f =
      F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) g := by
  obtain ⟨r, hr⟩ := (F.orbit_map_eq_iff f g).mp same
  have hg : g = f ≫ F.inner Q r := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    exact hr x
  rw [hg, hcomp, F.nativeCohomologyRawPush_inner, LinearMap.id_comp]

theorem nativeCohomologyOrbitPush_raw {P Q : F.Object} (f : P ⟶ Q) :
    F.nativeCohomologyOrbitPush (R := R) (A := A) n (F.toOrbit.map f) =
      F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) f :=
  F.nativeCohomologyRawPush_same_orbit n hcomp _ _ (F.orbitRepresentative_map _)

theorem nativeCohomologyOrbitPush_id (P : F.Orbit) :
    F.nativeCohomologyOrbitPush (R := R) (A := A) n (𝟙 P) = LinearMap.id := by
  have same : F.toOrbit.map (F.orbitRepresentative (𝟙 P)) = F.toOrbit.map (𝟙 P.as) := by
    rw [F.orbitRepresentative_map, F.toOrbit.map_id]
    rfl
  exact (F.nativeCohomologyRawPush_same_orbit n hcomp _ _ same).trans
    (F.nativeCohomologyRawPush_id n P.as)

theorem nativeCohomologyOrbitPush_comp {P Q T : F.Orbit} (f : P ⟶ Q) (g : Q ⟶ T) :
    F.nativeCohomologyOrbitPush (R := R) (A := A) n (f ≫ g) =
      (F.nativeCohomologyOrbitPush n g).comp (F.nativeCohomologyOrbitPush n f) := by
  have same : F.toOrbit.map (F.orbitRepresentative (f ≫ g)) =
      F.toOrbit.map (F.orbitRepresentative f ≫ F.orbitRepresentative g) := by
    rw [F.orbitRepresentative_map, F.toOrbit.map_comp,
      F.orbitRepresentative_map, F.orbitRepresentative_map]
    rfl
  exact (F.nativeCohomologyRawPush_same_orbit n hcomp _ _ same).trans (hcomp _ _)

theorem nativeCohomologyOrbit_pull_iso {P Q : F.Orbit} (f : P ⟶ Q) [IsIso f] :
    F.groupCohomologyOrbitPull (R := R) (A := A) (n := n) f =
      F.nativeCohomologyOrbitPush n (inv f) := by
  let e := F.isoOfEqualOrder (F.orbitRepresentative f)
    (le_antisymm (F.orbitOrder_mono f) (F.orbitOrder_mono (inv f)))
  have he : F.toOrbit.map e.hom = f := F.orbitRepresentative_map f
  have hei : F.toOrbit.map e.inv = inv f := by
    apply IsIso.eq_inv_of_hom_inv_id (f := f)
    calc
      f ≫ F.toOrbit.map e.inv = F.toOrbit.map e.hom ≫ F.toOrbit.map e.inv :=
        congrArg (fun t => t ≫ F.toOrbit.map e.inv) he.symm
      _ = F.toOrbit.map (e.hom ≫ e.inv) := (F.toOrbit.map_comp _ _).symm
      _ = 𝟙 _ := (congrArg (fun t => F.toOrbit.map t) e.hom_inv_id).trans
        (F.toOrbit.map_id _)
  have same : F.toOrbit.map e.inv = F.toOrbit.map (F.orbitRepresentative (inv f)) :=
    hei.trans (F.orbitRepresentative_map _).symm
  exact (F.nativeGroupCohomologyRawPush_iso e.symm n).symm.trans
    (F.nativeCohomologyRawPush_same_orbit n hcomp _ _ same)

/-- Genuine native values, pullbacks and transfers, with no Mackey-identity premise. -/
def cohomologyFunctorDataOfPush : MackeyFunctorData.{u,u} R F.Orbit where
  Value P := OrdinaryCohomology.value R P.as.subgroup A n
  valueAddCommGroup _ := inferInstance
  valueModule _ := inferInstance
  pull := F.groupCohomologyOrbitPull
  push := F.nativeCohomologyOrbitPush n
  pull_id := F.cohomologyOrbitPull_id_of_inner n
    (F.cohomologyRawPull_inner_unconditional n)
  push_id := F.nativeCohomologyOrbitPush_id n hcomp
  pull_comp := F.cohomologyOrbitPull_comp_of_inner n
    (F.cohomologyRawPull_inner_unconditional n)
  push_comp := F.nativeCohomologyOrbitPush_comp n hcomp
  pull_iso f := by intro hf; exact F.nativeCohomologyOrbit_pull_iso n hcomp f

theorem cohomologyFunctorDataOfPush_pull_raw {P Q : F.Object} (f : P ⟶ Q) :
    (F.cohomologyFunctorDataOfPush n hcomp).pull (F.toOrbit.map f) =
      F.groupCohomologyRawPull (R := R) (A := A) f n :=
  F.cohomologyOrbitPull_raw_of_inner n (F.cohomologyRawPull_inner_unconditional n) f

theorem cohomologyFunctorDataOfPush_push_raw {P Q : F.Object} (f : P ⟶ Q) :
    (F.cohomologyFunctorDataOfPush n hcomp).push (F.toOrbit.map f) =
      F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (A := A) n) f :=
  F.nativeCohomologyOrbitPush_raw n hcomp f

end Sharpness.FusionSystem
