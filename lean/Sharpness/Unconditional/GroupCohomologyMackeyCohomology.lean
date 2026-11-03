import Sharpness.Unconditional.GroupCohomologyMackeyTrace
import Sharpness.Unconditional.GroupCohomologyShapiroMap
import Sharpness.Unconditional.GroupCohomologyFunctor
import Sharpness.Unconditional.GroupCohomologyInnerCoefficients

/-! The actual native-cohomology double-coset formula. Coinduction components
are identified through the forward Shapiro map and corrected inner conjugation;
the representation-level trace identity then supplies the transfer formula. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology.MackeyDecomposition
open CategoryTheory
open scoped BigOperators

variable {R G A : Type u} [CommRing R] [Group G]
    [AddCommGroup A] [Module R A] (H K : Subgroup G)

/-- The actual conjugation from K intersect x-inverse H x to H. -/
def intersectionConjugation (x : G) : intersection H K x →* H where
  toFun l := ⟨x * (l.1 : G) * x⁻¹, l.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

/-- Evaluate the double-coset component at its identity. -/
def componentEvaluation (d : DoubleCoset.Quotient (H : Set G) K) :
    Rep.res (K.subtype.comp (intersection H K d.out).subtype)
      (Rep.coind H.subtype (Rep.trivial R H A)) ⟶
        Rep.trivial R (intersection H K d.out) A :=
  (Rep.resFunctor (intersection H K d.out).subtype).map (componentHom H K d) ≫
    ((Rep.resCoindAdjunction.{u} R (intersection H K d.out).subtype).counit.app
      (Rep.trivial R (intersection H K d.out) A))

@[simp] theorem componentEvaluation_apply (d : DoubleCoset.Quotient (H : Set G) K)
    (f : Source (R := R) (A := A) H) :
    (componentEvaluation H K d).hom f = f.1 d.out := by
  change f.1 (d.out * 1) = f.1 d.out
  rw [mul_one]

/-- Shapiro on a component is restriction followed by evaluation at d. -/
theorem restriction_component_shapiro (d : DoubleCoset.Quotient (H : Set G) K)
    (n : ℕ) :
    groupCohomology.map K.subtype
        (𝟙 (Rep.res K.subtype (Rep.coind H.subtype (Rep.trivial R H A)))) n ≫
      groupCohomology.map (MonoidHom.id K) (componentHom H K d) n ≫
      (groupCohomology.coindIso (Rep.trivial R (intersection H K d.out) A) n).hom =
      groupCohomology.map (K.subtype.comp (intersection H K d.out).subtype)
        (componentEvaluation H K d) n := by
  rw [coindIso_hom_eq_map]
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  rfl

/-- Corrected inner conjugation changes evaluation at d into evaluation at one.
This is an equality of the actual inhomogeneous cochain maps. -/
theorem component_conjugation_cochains
    (d : DoubleCoset.Quotient (H : Set G) K) :
    groupCohomology.cochainsMap (MulAut.conj d.out).toMonoidHom
        (conjugationCoefficientHom (Rep.coind H.subtype (Rep.trivial R H A)) d.out) ≫
      groupCohomology.cochainsMap
        (K.subtype.comp (intersection H K d.out).subtype) (componentEvaluation H K d) =
      groupCohomology.cochainsMap H.subtype
        ((Rep.resCoindAdjunction.{u} R H.subtype).counit.app (Rep.trivial R H A)) ≫
        cochainPull (intersectionConjugation H K d.out) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext z
  change (x (fun i => d.out * ((z i).1 : G) * d.out⁻¹)).1 ((d.out * 1) * d.out⁻¹) =
    (x (fun i => d.out * ((z i).1 : G) * d.out⁻¹)).1 1
  rw [mul_one, mul_inv_cancel]

/-- The component/Shapiro square uses the actual native restriction along
conjugation into H; no Mackey identity is supplied as an assumption. -/
theorem component_shapiro_square (d : DoubleCoset.Quotient (H : Set G) K)
    (n : ℕ) :
    groupCohomology.map K.subtype
        (𝟙 (Rep.res K.subtype (Rep.coind H.subtype (Rep.trivial R H A)))) n ≫
      groupCohomology.map (MonoidHom.id K) (componentHom H K d) n ≫
      (groupCohomology.coindIso (Rep.trivial R (intersection H K d.out) A) n).hom =
      (groupCohomology.coindIso (Rep.trivial R H A) n).hom ≫
        pull (intersectionConjugation H K d.out) n := by
  rw [restriction_component_shapiro, coindIso_hom_eq_map]
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (component_conjugation_cochains (R := R) (A := A) H K d)
  simp only [HomologicalComplex.homologyMap_comp] at h
  change groupCohomology.map (MulAut.conj d.out).toMonoidHom
      (conjugationCoefficientHom (Rep.coind H.subtype (Rep.trivial R H A)) d.out) n ≫
      groupCohomology.map (K.subtype.comp (intersection H K d.out).subtype)
        (componentEvaluation H K d) n =
      groupCohomology.map H.subtype
        ((Rep.resCoindAdjunction.{u} R H.subtype).counit.app (Rep.trivial R H A)) n ≫
        pull (intersectionConjugation H K d.out) n at h
  rw [map_inner_coefficients, Category.id_comp] at h
  exact h

/-- Coefficient maps commute with the actual restriction of cochains. -/
theorem native_map_restriction_naturality {V W : Rep.{u} R G} (f : V ⟶ W)
    (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) f n ≫
        groupCohomology.map K.subtype (𝟙 (Rep.res K.subtype W)) n =
      groupCohomology.map K.subtype (𝟙 (Rep.res K.subtype V)) n ≫
        groupCohomology.map (MonoidHom.id K) ((Rep.resFunctor K.subtype).map f) n := by
  simp only [groupCohomology.map, ← HomologicalComplex.homologyMap_comp]
  rfl

variable [Finite G]

local instance nativeDoubleCosetFintype : Fintype (DoubleCoset.Quotient (H : Set G) K) := by
  unfold DoubleCoset.Quotient
  exact Fintype.ofFinite _

/-- Each actual coinduction trace component induces the conjugation-restriction
followed by the transfer from its intersection subgroup. -/
theorem native_component_trace (d : DoubleCoset.Quotient (H : Set G) K) (n : ℕ) :
    groupCohomology.map K.subtype
        (𝟙 (Rep.res K.subtype (Rep.coind H.subtype (Rep.trivial R H A)))) n ≫
      groupCohomology.map (MonoidHom.id K)
        (componentHom H K d ≫
          coinductionTrace (intersection H K d.out) (Rep.trivial R K A)) n =
      (groupCohomology.coindIso (Rep.trivial R H A) n).hom ≫
        pull (intersectionConjugation H K d.out) n ≫
          transfer (intersection H K d.out) n := by
  calc
    _ = (groupCohomology.map K.subtype
          (𝟙 (Rep.res K.subtype (Rep.coind H.subtype (Rep.trivial R H A)))) n ≫
        groupCohomology.map (MonoidHom.id K) (componentHom H K d) n ≫
          (groupCohomology.coindIso (Rep.trivial R (intersection H K d.out) A) n).hom) ≫
            corestriction (intersection H K d.out) (Rep.trivial R K A) n := by
      rw [groupCohomology.map_id_comp, ← shapiro_corestriction]
      simp only [Category.assoc]
      rfl
    _ = _ := by
      rw [component_shapiro_square]
      rfl

/-- The double-coset formula for the actual native cohomology restriction and
transfer, for every degree and every trivial module over a commutative ring. -/
theorem transfer_pull_doubleCoset (n : ℕ) :
    transfer (R := R) (A := A) H n ≫ pull K.subtype n =
      ∑ d : DoubleCoset.Quotient (H : Set G) K,
        pull (intersectionConjugation H K d.out) n ≫
          transfer (intersection H K d.out) n := by
  apply (cancel_epi (groupCohomology.coindIso (Rep.trivial R H A) n).hom).mp
  rw [← Category.assoc]
  change ((groupCohomology.coindIso (Rep.trivial R H A) n).hom ≫
      corestriction H (Rep.trivial R G A) n) ≫
      groupCohomology.map K.subtype (𝟙 (Rep.res K.subtype (Rep.trivial R G A))) n = _
  have hs : (groupCohomology.coindIso (Rep.trivial R H A) n).hom ≫
      corestriction H (Rep.trivial R G A) n =
      groupCohomology.map (MonoidHom.id G) (coinductionTrace H (Rep.trivial R G A)) n :=
    shapiro_corestriction H (Rep.trivial R G A) n
  rw [hs, native_map_restriction_naturality,
    coinductionTrace_doubleCoset]
  simp only [nativeCohomology_map_sum, Preadditive.comp_sum,
    native_component_trace]

end Sharpness.OrdinaryCohomology.MackeyDecomposition
