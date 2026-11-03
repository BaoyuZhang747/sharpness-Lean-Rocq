import Sharpness.V29.SimpleConjugacyClasses

/-!
The trace-image decomposition of a given simple full Mackey functor.
The finite product is the finite direct sum in Díaz–Park formula (4).
Surjectivity uses the full Mackey formula and transfer generation.
Injectivity uses kernel-subfunctor stability and simplicity directly;
none of the old restriction-detection conclusions is used.
-/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (hM : M.IsSimple) (Q : Subgroup S) (hQ : F.IsMinimalSupport M Q)

include hM hQ

/-- The summand is the image of the relative normalizer trace on the actual
outer-automorphism module at the chosen representative. -/
def simpleTraceSummand (U : Subgroup S) (c : F.SimpleConjugacyClass Q U) :
    Submodule k (M.Value (F.toOrbit.obj ⟨(F.simpleClassRepresentative c).val⟩)) :=
  LinearMap.range (F.normalizerTrace M U (F.simpleClassRepresentative c).val)

def SimpleTraceValue (U : Subgroup S) : Type u :=
  (c : F.SimpleConjugacyClass Q U) → F.simpleTraceSummand M Q U c

instance (U : Subgroup S) : AddCommGroup (F.SimpleTraceValue M Q U) :=
  inferInstanceAs (AddCommGroup ((c : F.SimpleConjugacyClass Q U) →
    F.simpleTraceSummand M Q U c))

instance (U : Subgroup S) : Module k (F.SimpleTraceValue M Q U) :=
  inferInstanceAs (Module k ((c : F.SimpleConjugacyClass Q U) →
    F.simpleTraceSummand M Q U c))

def simpleTraceCoordinates (U : Subgroup S) :
    M.Value (F.toOrbit.obj ⟨U⟩) →ₗ[k] F.SimpleTraceValue M Q U where
  toFun x c := ⟨M.pull (F.minimalInclusion (F.simpleClassRepresentative c)) x, by
    apply F.diazParkTraceInput.equations_4_6 M
      (F.simpleLabelAtMinimalSupport M hM Q hQ) U
      (F.simpleClassRepresentative c).val
      (F.simpleClassRepresentative c).property.1
      (F.simpleClassRepresentative c).property.2
    exact ⟨x, rfl⟩⟩
  map_add' x y := by apply funext; intro c; apply Subtype.ext; exact map_add _ _ _
  map_smul' a x := by apply funext; intro c; apply Subtype.ext; exact map_smul _ _ _

@[simp] theorem simpleTraceCoordinates_apply (U : Subgroup S)
    (x : M.Value (F.toOrbit.obj ⟨U⟩)) (c : F.SimpleConjugacyClass Q U) :
    (F.simpleTraceCoordinates M hM Q hQ U x c).val =
      M.pull (F.minimalInclusion (F.simpleClassRepresentative c)) x := rfl

/-- Different subgroup-conjugacy classes have zero cross restriction-transfer
composite. This is the off-diagonal part of formula (6). -/
theorem simple_cross_transfer_zero {U : Subgroup S}
    (L K : F.SimpleInclusion Q U) (hLK : F.simpleClass L ≠ F.simpleClass K) :
    (M.pull (F.minimalInclusion L)).comp (M.push (F.minimalInclusion K)) = 0 := by
  apply F.minimal_mackey_raw_eq_zero M
    (F.simpleLabelAtMinimalSupport M hM Q hQ)
    (F.inclusion (P := ⟨L.val⟩) (Q := ⟨U⟩) L.property.1)
    (F.inclusion (P := ⟨K.val⟩) (Q := ⟨U⟩) K.property.1)
    (F.simpleInclusion_card L)
  intro t ht
  have hfull := F.inclusion_spanApex_eq_of_order L.property.1 K.property.1 t
    (ht.trans (F.simpleInclusion_card L).symm)
  exact hLK ((F.simpleClass_eq_iff L K).mpr
    (F.simpleInsideConjugate_of_fullSpan L K t hfull))

theorem simpleTraceCoordinates_surjective (U : Subgroup S) :
    Function.Surjective (F.simpleTraceCoordinates M hM Q hQ U) := by
  classical
  letI : Fintype (F.SimpleConjugacyClass Q U) := Fintype.ofFinite _
  intro w
  let y (c : F.SimpleConjugacyClass Q U) := Classical.choose (w c).property
  have hy (c : F.SimpleConjugacyClass Q U) :
      F.normalizerTrace M U (F.simpleClassRepresentative c).val (y c) = (w c).val :=
    Classical.choose_spec (w c).property
  refine ⟨∑ c, M.push (F.minimalInclusion (F.simpleClassRepresentative c)) (y c), ?_⟩
  apply funext
  intro c
  apply Subtype.ext
  change M.pull (F.minimalInclusion (F.simpleClassRepresentative c))
    (∑ d, M.push (F.minimalInclusion (F.simpleClassRepresentative d)) (y d)) = (w c).val
  rw [map_sum]
  rw [Finset.sum_eq_single c]
  · have hself := F.minimal_self_mackey_eq_normalizerTrace M
      (F.simpleLabelAtMinimalSupport M hM Q hQ)
      (F.simpleClassRepresentative c).property.1
      (F.simpleClassRepresentative c).property.2
    exact (LinearMap.congr_fun hself (y c)).trans (hy c)
  · intro d _ hdc
    have hne : F.simpleClass (F.simpleClassRepresentative c) ≠
        F.simpleClass (F.simpleClassRepresentative d) := by simpa using Ne.symm hdc
    exact LinearMap.congr_fun
      (F.simple_cross_transfer_zero M hM Q hQ _ _ hne) (y d)
  · simp

/-- Restriction at an unchosen representative is obtained from the chosen
one by the proved orbit-category conjugation triangle. -/
theorem simple_restriction_zero_of_coordinates_zero (U : Subgroup S)
    (x : M.Value (F.toOrbit.obj ⟨U⟩))
    (hx : F.simpleTraceCoordinates M hM Q hQ U x = 0)
    (L : F.SimpleInclusion Q U) : M.pull (F.minimalInclusion L) x = 0 := by
  let c := F.simpleClass L
  let R := F.simpleClassRepresentative c
  have hc : F.simpleClass R = F.simpleClass L := F.simpleClass_representative c
  have hR : M.pull (F.minimalInclusion R) x = 0 :=
    congrArg Subtype.val (congrFun hx c)
  let e := F.simpleInsideTransport R L ((F.simpleClass_eq_iff R L).mp hc)
  have he : e.hom ≫ F.minimalInclusion L = F.minimalInclusion R :=
    F.simpleInsideTransport_inclusion R L _
  have hf : F.minimalInclusion L = e.inv ≫ F.minimalInclusion R := by
    rw [← he, Iso.inv_hom_id_assoc]
  rw [hf, M.pull_comp, LinearMap.comp_apply, hR, map_zero]

/-- The injectivity part of the trace decomposition is proved from the
actual Mackey kernel subfunctor, without an assumed detection theorem. -/
theorem simpleTraceCoordinates_zero (U : Subgroup S)
    (x : M.Value (F.toOrbit.obj ⟨U⟩))
    (hx : F.simpleTraceCoordinates M hM Q hQ U x = 0) : x = 0 := by
  let q := F.toOrbit.obj ⟨Q⟩
  have hsmall : ∀ P : F.Orbit, F.orbitOrder P < F.orbitOrder q →
      ∀ y : M.Value P, y = 0 :=
    fun P h => F.minimalSupport_small_zero M hM Q hQ P.as.subgroup h
  let N := M.detectedSubfunctor q hsmall
  have hxN : x ∈ N.obj (F.toOrbit.obj ⟨U⟩) := by
    apply (M.mem_detectedKernel_iff q).mpr
    intro s
    let L : F.SimpleInclusion Q U :=
      ⟨F.arrowImage s.2.2, F.arrowImage_le s.2.2,
        ⟨s.2.1.trans (F.arrowImageIso s.2.2)⟩⟩
    have hL := F.simple_restriction_zero_of_coordinates_zero M hM Q hQ U x hx L
    rw [← F.arrow_factorization s.2.2, M.pull_comp, LinearMap.comp_apply]
    change M.pull (F.arrowImageIso s.2.2).hom (M.pull (F.minimalInclusion L) x) = 0
    rw [hL, map_zero]
  rcases hM.2 N with hbot | htop
  · have h := hbot (F.toOrbit.obj ⟨U⟩)
    rw [h] at hxN
    exact hxN
  · obtain ⟨y, hy⟩ := hQ.1
    have hyN : y ∈ N.obj q := by rw [htop q]; trivial
    have hz := (M.mem_detectedKernel_iff q).mp hyN ⟨q, Iso.refl q, 𝟙 q⟩
    rw [M.pull_id] at hz
    exact (hy hz).elim

theorem simpleTraceCoordinates_injective (U : Subgroup S) :
    Function.Injective (F.simpleTraceCoordinates M hM Q hQ U) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply F.simpleTraceCoordinates_zero M hM Q hQ U
  rw [map_sub, hxy, sub_self]

/-- Formula (4): the actual simple value is the finite sum of trace-image
summands, with coordinates given by the actual restrictions. -/
def simpleTraceEquiv (U : Subgroup S) :
    M.Value (F.toOrbit.obj ⟨U⟩) ≃ₗ[k] F.SimpleTraceValue M Q U :=
  LinearEquiv.ofBijective (F.simpleTraceCoordinates M hM Q hQ U)
    ⟨F.simpleTraceCoordinates_injective M hM Q hQ U,
      F.simpleTraceCoordinates_surjective M hM Q hQ U⟩

theorem simple_restriction_detection_v29 (U : Subgroup S)
    (x : M.Value (F.toOrbit.obj ⟨U⟩))
    (hx : ∀ (L : Subgroup S) (hLU : L ≤ U), F.isoSystem.IsConjugate Q L →
      M.pull (F.toOrbit.map (F.inclusion hLU)) x = 0) : x = 0 := by
  apply (F.simpleTraceEquiv M hM Q hQ U).injective
  change F.simpleTraceCoordinates M hM Q hQ U x = F.simpleTraceCoordinates M hM Q hQ U 0
  rw [map_zero]
  funext c
  apply Subtype.ext
  exact hx (F.simpleClassRepresentative c).val (F.simpleClassRepresentative c).property.1
    ((F.isConjugate_iff_orbit_iso Q _).mpr (F.simpleClassRepresentative c).property.2)

theorem simple_value_zero_v29 (U : Subgroup S)
    (hnone : ∀ L : Subgroup S, F.isoSystem.IsConjugate Q L → ¬ L ≤ U)
    (x : M.Value (F.toOrbit.obj ⟨U⟩)) : x = 0 := by
  apply F.simple_restriction_detection_v29 M hM Q hQ U x
  intro L hLU hL
  exact (hnone L hL hLU).elim

end Sharpness.FusionSystem
