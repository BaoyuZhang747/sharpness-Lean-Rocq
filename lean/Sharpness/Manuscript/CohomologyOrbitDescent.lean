import Sharpness.GroupCohomologyOrbit
import Sharpness.HigherLimits

/-! Descent of native ordinary group cohomology using only inner invariance.
No transfer map or Mackey identity is needed to define this contravariant
coefficient functor. The inner-invariance hypothesis is separated here so that
the unconditional constructor can instantiate it with its independent proof. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory Opposite
variable {S R : Type u} [Group S] [Finite S] [CommRing R] (F : FusionSystem S)
    {A : Type u} [AddCommGroup A] [Module R A] (n : ℕ)

variable (hinner : ∀ (P : F.Object) (r : P.subgroup),
    F.groupCohomologyRawPull (R := R) (A := A) (F.inner P r) n = LinearMap.id)

include hinner

theorem cohomologyRawPull_same_orbit_of_inner {P Q : F.Object} (f g : P ⟶ Q)
    (same : F.toOrbit.map f = F.toOrbit.map g) :
    F.groupCohomologyRawPull (R := R) (A := A) f n = F.groupCohomologyRawPull g n := by
  obtain ⟨r, hr⟩ := (F.orbit_map_eq_iff f g).mp same
  have hg : g = f ≫ F.inner Q r := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    exact hr x
  rw [hg, F.groupCohomologyRawPull_comp, hinner, LinearMap.comp_id]

theorem cohomologyOrbitPull_raw_of_inner {P Q : F.Object} (f : P ⟶ Q) :
    F.groupCohomologyOrbitPull (R := R) (A := A) (n := n) (F.toOrbit.map f) =
      OrdinaryCohomology.pullLinear f.val n :=
  F.cohomologyRawPull_same_orbit_of_inner n hinner _ _ (F.orbitRepresentative_map _)

theorem cohomologyOrbitPull_id_of_inner (P : F.Orbit) :
    F.groupCohomologyOrbitPull (R := R) (A := A) (n := n) (𝟙 P) = LinearMap.id := by
  have same : F.toOrbit.map (F.orbitRepresentative (𝟙 P)) = F.toOrbit.map (𝟙 P.as) := by
    rw [F.orbitRepresentative_map, F.toOrbit.map_id]
    rfl
  exact (F.cohomologyRawPull_same_orbit_of_inner n hinner _ _ same).trans
    (F.groupCohomologyRawPull_id P.as n)

theorem cohomologyOrbitPull_comp_of_inner {P Q T : F.Orbit} (f : P ⟶ Q) (g : Q ⟶ T) :
    F.groupCohomologyOrbitPull (R := R) (A := A) (n := n) (f ≫ g) =
      (F.groupCohomologyOrbitPull f).comp (F.groupCohomologyOrbitPull g) := by
  have same : F.toOrbit.map (F.orbitRepresentative (f ≫ g)) =
      F.toOrbit.map (F.orbitRepresentative f ≫ F.orbitRepresentative g) := by
    rw [F.orbitRepresentative_map, F.toOrbit.map_comp,
      F.orbitRepresentative_map, F.orbitRepresentative_map]
    rfl
  exact (F.cohomologyRawPull_same_orbit_of_inner n hinner _ _ same).trans
    (F.groupCohomologyRawPull_comp _ _ n)

/-- Actual cohomology values and pullbacks, with descent requiring only inner
invariance. This intermediate definition does not assume a transfer structure. -/
def cohomologyOrbitCoefficientOfInner : CoefficientCategory R F.Orbit where
  obj P := OrdinaryCohomology.value R P.unop.as.subgroup A n
  map f := ModuleCat.ofHom (F.groupCohomologyOrbitPull f.unop)
  map_id P := by
    apply ModuleCat.hom_ext
    exact F.cohomologyOrbitPull_id_of_inner n hinner P.unop
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact F.cohomologyOrbitPull_comp_of_inner n hinner g.unop f.unop

def cohomologyCoefficientOfInner : CoefficientCategory R F.CentricOrbit :=
  F.centricInclusion.op ⋙ F.cohomologyOrbitCoefficientOfInner n hinner

theorem cohomologyOrbitCoefficientOfInner_map_raw {P Q : F.Object} (f : P ⟶ Q) :
    (F.cohomologyOrbitCoefficientOfInner n hinner).map (F.toOrbit.map f).op =
      OrdinaryCohomology.pull (R := R) (A := A) f.val n := by
  apply ModuleCat.hom_ext
  exact F.cohomologyOrbitPull_raw_of_inner n hinner f

end Sharpness.FusionSystem
