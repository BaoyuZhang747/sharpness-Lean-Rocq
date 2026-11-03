import Sharpness.GroupCohomologyOrbit

/-! Both functor structures on the actual fusion orbit category,
including the isomorphism law proved by lifting an orbit isomorphism
to an actual subgroup isomorphism. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S R : Type u} [Group S] [Finite S] [CommRing R] (F : FusionSystem S)
    {A : Type u} [AddCommGroup A] [Module R A]
    {n : ℕ} (I : F.GroupCohomologyTransferLaws (R := R) A n)

include I

theorem groupCohomologyOrbitPull_id (P : F.Orbit) :
    F.groupCohomologyOrbitPull (R := R) (A := A) (n := n) (𝟙 P) = LinearMap.id := by
  have same : F.toOrbit.map (F.orbitRepresentative (𝟙 P)) = F.toOrbit.map (𝟙 P.as) := by
    rw [F.orbitRepresentative_map, F.toOrbit.map_id]
    rfl
  exact (F.groupCohomologyRawPull_same_orbit I _ _ same).trans (F.groupCohomologyRawPull_id P.as n)

theorem groupCohomologyOrbitPush_id (P : F.Orbit) :
    F.groupCohomologyOrbitPush I (𝟙 P) = LinearMap.id := by
  have same : F.toOrbit.map (F.orbitRepresentative (𝟙 P)) = F.toOrbit.map (𝟙 P.as) := by
    rw [F.orbitRepresentative_map, F.toOrbit.map_id]
    rfl
  exact (F.groupCohomologyRawPush_same_orbit I _ _ same).trans (F.groupCohomologyRawPush_id I P.as)

theorem groupCohomologyOrbitPull_comp {P Q T : F.Orbit} (f : P ⟶ Q) (g : Q ⟶ T) :
    F.groupCohomologyOrbitPull (R := R) (A := A) (n := n) (f ≫ g) =
      (F.groupCohomologyOrbitPull f).comp (F.groupCohomologyOrbitPull g) := by
  have same : F.toOrbit.map (F.orbitRepresentative (f ≫ g)) =
      F.toOrbit.map (F.orbitRepresentative f ≫ F.orbitRepresentative g) := by
    rw [F.orbitRepresentative_map, F.toOrbit.map_comp,
      F.orbitRepresentative_map, F.orbitRepresentative_map]
    rfl
  exact (F.groupCohomologyRawPull_same_orbit I _ _ same).trans (F.groupCohomologyRawPull_comp _ _ n)

theorem groupCohomologyOrbitPush_comp {P Q T : F.Orbit} (f : P ⟶ Q) (g : Q ⟶ T) :
    F.groupCohomologyOrbitPush I (f ≫ g) =
      (F.groupCohomologyOrbitPush I g).comp (F.groupCohomologyOrbitPush I f) := by
  have same : F.toOrbit.map (F.orbitRepresentative (f ≫ g)) =
      F.toOrbit.map (F.orbitRepresentative f ≫ F.orbitRepresentative g) := by
    rw [F.orbitRepresentative_map, F.toOrbit.map_comp,
      F.orbitRepresentative_map, F.orbitRepresentative_map]
    rfl
  exact (F.groupCohomologyRawPush_same_orbit I _ _ same).trans (I.transfer_comp _ _)

theorem groupCohomologyOrbit_pull_iso {P Q : F.Orbit} (f : P ⟶ Q) [IsIso f] :
    F.groupCohomologyOrbitPull (R := R) (A := A) (n := n) f = F.groupCohomologyOrbitPush I (inv f) := by
  let e := F.isoOfEqualOrder (F.orbitRepresentative f)
    (le_antisymm (F.orbitOrder_mono f) (F.orbitOrder_mono (inv f)))
  have he : F.toOrbit.map e.hom = f := F.orbitRepresentative_map f
  have hei : F.toOrbit.map e.inv = inv f := by
    apply IsIso.eq_inv_of_hom_inv_id (f := f)
    calc
      f ≫ F.toOrbit.map e.inv = F.toOrbit.map e.hom ≫ F.toOrbit.map e.inv :=
        congrArg (fun t => t ≫ F.toOrbit.map e.inv) he.symm
      _ = F.toOrbit.map (e.hom ≫ e.inv) := (F.toOrbit.map_comp _ _).symm
      _ = 𝟙 _ := (congrArg (fun t => F.toOrbit.map t) e.hom_inv_id).trans (F.toOrbit.map_id _)
  have same : F.toOrbit.map e.inv = F.toOrbit.map (F.orbitRepresentative (inv f)) :=
    hei.trans (F.orbitRepresentative_map _).symm
  exact (I.transfer_iso e.symm).symm.trans
    (F.groupCohomologyRawPush_same_orbit I _ _ same)

def groupCohomologyFunctorData : MackeyFunctorData.{u,u} R F.Orbit where
  Value P := OrdinaryCohomology.value R P.as.subgroup A n
  valueAddCommGroup _ := inferInstance
  valueModule _ := inferInstance
  pull := F.groupCohomologyOrbitPull
  push := F.groupCohomologyOrbitPush I
  pull_id := F.groupCohomologyOrbitPull_id I
  push_id := F.groupCohomologyOrbitPush_id I
  pull_comp := F.groupCohomologyOrbitPull_comp I
  push_comp := F.groupCohomologyOrbitPush_comp I
  pull_iso f := by intro hf; exact F.groupCohomologyOrbit_pull_iso I f

end Sharpness.FusionSystem
