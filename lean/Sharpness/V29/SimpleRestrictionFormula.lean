import Sharpness.V29.SimpleFunctor

/-! Díaz–Park formula (6) for arbitrary subgroup inclusions. Each output
coordinate is the input coordinate of its ambient conjugacy class, with
the actual conjugation transport between the chosen representatives. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

def simpleInclusionOvergroup {Q U V : Subgroup S} (hUV : U ≤ V)
    (L : F.SimpleInclusion Q U) : F.SimpleInclusion Q V :=
  ⟨L.val, L.property.1.trans hUV, L.property.2⟩

def simpleClassOvergroup {Q U V : Subgroup S} (hUV : U ≤ V) :
    F.SimpleConjugacyClass Q U → F.SimpleConjugacyClass Q V :=
  Quotient.map (F.simpleInclusionOvergroup hUV) (by
    intro L K h
    obtain ⟨t, ht⟩ := h
    exact ⟨⟨t.val, hUV t.property⟩, ht⟩)

@[simp] theorem simpleClassOvergroup_mk {Q U V : Subgroup S} (hUV : U ≤ V)
    (L : F.SimpleInclusion Q U) :
    F.simpleClassOvergroup hUV (F.simpleClass L) =
      F.simpleClass (F.simpleInclusionOvergroup hUV L) := rfl

theorem simpleClassOvergroup_representative {Q U V : Subgroup S} (hUV : U ≤ V)
    (c : F.SimpleConjugacyClass Q U) :
    F.simpleClass (F.simpleInclusionOvergroup hUV (F.simpleClassRepresentative c)) =
      F.simpleClassOvergroup hUV c := by
  rw [← F.simpleClassOvergroup_mk, F.simpleClass_representative]

def simpleRestrictionTransport {Q U V : Subgroup S} (hUV : U ≤ V)
    (c : F.SimpleConjugacyClass Q U) :
    F.toOrbit.obj ⟨(F.simpleClassRepresentative (F.simpleClassOvergroup hUV c)).val⟩ ≅
      F.toOrbit.obj ⟨(F.simpleClassRepresentative c).val⟩ :=
  F.simpleInsideTransport
    (F.simpleClassRepresentative (F.simpleClassOvergroup hUV c))
    (F.simpleInclusionOvergroup hUV (F.simpleClassRepresentative c))
    ((F.simpleClass_eq_iff _ _).mp ((F.simpleClass_representative _).trans
      (F.simpleClassOvergroup_representative hUV c).symm))

variable {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (hM : M.IsSimple) (Q : Subgroup S) (hQ : F.IsMinimalSupport M Q)

include hM hQ

/-- The full restriction-coordinate formula: the map is diagonal on
subgroup classes, with fusion conjugation on representative modules. -/
theorem simple_restriction_coordinate {U V : Subgroup S} (hUV : U ≤ V)
    (x : M.Value (F.toOrbit.obj ⟨V⟩)) (c : F.SimpleConjugacyClass Q U) :
    (F.simpleTraceEquiv M hM Q hQ U
      (M.pull (F.toOrbit.map (F.inclusion hUV)) x) c).val =
    M.pull (F.simpleRestrictionTransport hUV c).inv
      ((F.simpleTraceEquiv M hM Q hQ V x (F.simpleClassOvergroup hUV c)).val) := by
  let R := F.simpleClassRepresentative c
  let R' := F.simpleInclusionOvergroup hUV R
  let J := F.simpleClassRepresentative (F.simpleClassOvergroup hUV c)
  let e := F.simpleRestrictionTransport hUV c
  have hcomp : F.minimalInclusion R ≫ F.toOrbit.map (F.inclusion hUV) =
      F.minimalInclusion R' := by
    change F.toOrbit.map (F.inclusion R.property.1) ≫
      F.toOrbit.map (F.inclusion hUV) =
      F.toOrbit.map (F.inclusion (R.property.1.trans hUV))
    rw [← F.toOrbit.map_comp]
    rfl
  have he : e.hom ≫ F.minimalInclusion R' = F.minimalInclusion J :=
    F.simpleInsideTransport_inclusion J R' _
  have hf : F.minimalInclusion R' = e.inv ≫ F.minimalInclusion J := by
    rw [← he, Iso.inv_hom_id_assoc]
  change M.pull (F.minimalInclusion R) (M.pull (F.toOrbit.map (F.inclusion hUV)) x) =
    M.pull e.inv (M.pull (F.minimalInclusion J) x)
  rw [← LinearMap.comp_apply, ← M.pull_comp, hcomp, hf, M.pull_comp]
  rfl

/-- A summand has zero restriction coordinates at all classes not lying
in its ambient conjugacy class. The remaining coordinates are the
conjugation transports of that summand, as in formula (6). -/
theorem simple_restriction_other_coordinate {U V : Subgroup S} (hUV : U ≤ V)
    (c : F.SimpleConjugacyClass Q U) (d : F.SimpleConjugacyClass Q V)
    (hcd : F.simpleClassOvergroup hUV c ≠ d)
    (x : F.simpleTraceSummand M Q V d) :
    (F.simpleTraceEquiv M hM Q hQ U
      (M.pull (F.toOrbit.map (F.inclusion hUV))
        (F.simpleSummandInjection M hM Q hQ V d x)) c).val = 0 := by
  rw [F.simple_restriction_coordinate M hM Q hQ hUV]
  change M.pull (F.simpleRestrictionTransport hUV c).inv
    (M.pull (F.minimalInclusion (F.simpleClassRepresentative (F.simpleClassOvergroup hUV c)))
      (F.simpleSummandInjection M hM Q hQ V d x)) = 0
  rw [F.simple_other_summand_restriction M hM Q hQ V _ d hcd x, map_zero]

/-- The manuscript detector through the actual full Mackey isomorphism to
the direct sum of trace images on the transported minimal module. -/
theorem simple_functor_restriction_detection_v29 (U : Subgroup S)
    (x : M.Value (F.toOrbit.obj ⟨U⟩))
    (hx : ∀ (L : Subgroup S) (hLU : L ≤ U), F.isoSystem.IsConjugate Q L →
      M.pull (F.toOrbit.map (F.inclusion hLU)) x = 0) : x = 0 := by
  have htrace : F.simpleTraceEquiv M hM Q hQ U x = 0 := by
    apply funext
    intro c
    apply Subtype.ext
    exact hx (F.simpleClassRepresentative c).val (F.simpleClassRepresentative c).property.1
      ((F.isConjugate_iff_orbit_iso Q _).mpr (F.simpleClassRepresentative c).property.2)
  let e := F.simpleFunctorAtMinimalIso M hM Q hQ
  have he : e.hom.app (F.toOrbit.obj ⟨U⟩) x = 0 := by
    change F.simpleDiazParkDirectSumEquiv M hM Q hQ U x = 0
    simp only [simpleDiazParkDirectSumEquiv, simpleDiazParkEquiv,
      LinearEquiv.trans_apply, htrace, map_zero]
  have hi := congrArg (fun f : M ⟶ M => f.app (F.toOrbit.obj ⟨U⟩) x) e.hom_inv_id
  change e.inv.app (F.toOrbit.obj ⟨U⟩) (e.hom.app (F.toOrbit.obj ⟨U⟩) x) = x at hi
  rw [he, map_zero] at hi
  exact hi.symm

theorem simple_functor_value_zero_v29 (U : Subgroup S)
    (hnone : ∀ L : Subgroup S, F.isoSystem.IsConjugate Q L → ¬ L ≤ U)
    (x : M.Value (F.toOrbit.obj ⟨U⟩)) : x = 0 := by
  apply F.simple_functor_restriction_detection_v29 M hM Q hQ U x
  intro L hLU hL
  exact (hnone L hL hLU).elim

end Sharpness.FusionSystem
