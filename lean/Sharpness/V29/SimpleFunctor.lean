import Sharpness.V29.SimpleTransportedModule
import Sharpness.MackeyCategory
import Mathlib.LinearAlgebra.DFinsupp

/-! Full Mackey transport of the trace-image decomposition, and the
summand/restriction formulas used in the v2.9 manuscript. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

namespace Sharpness.MackeyModule
open CategoryTheory
open scoped BigOperators

variable {R : Type u} [Ring R] {C : Type v} [Category.{v} C] {B : MackeyShape C}
    (M : MackeyModule.{u,v,w} R C B)
    (W : C → Type w) [∀ P, AddCommGroup (W P)] [∀ P, Module R (W P)]
    (e : ∀ P, M.Value P ≃ₗ[R] W P)

/-- Change values by actual linear equivalences, retaining both Mackey
variances and every term of the full double-coset formula. -/
def transportValues : MackeyModule.{u,v,w} R C B where
  Value := W
  valueAddCommGroup := inferInstance
  valueModule := inferInstance
  pull {P Q} f := (e P).toLinearMap.comp ((M.pull f).comp (e Q).symm.toLinearMap)
  push {P Q} f := (e Q).toLinearMap.comp ((M.push f).comp (e P).symm.toLinearMap)
  pull_id P := by ext x; simp [M.pull_id]
  push_id P := by ext x; simp [M.push_id]
  pull_comp f g := by ext x; simp [M.pull_comp]
  push_comp f g := by ext x; simp [M.push_comp]
  pull_iso f := by intro h; rw [M.pull_iso]
  mackey {P Q T} f g := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
    have hm := LinearMap.congr_fun (M.mackey f g) ((e Q).symm x)
    simp only [LinearMap.comp_apply, LinearMap.sum_apply] at hm
    rw [hm, map_sum]

def transportValuesIso : M ≅ M.transportValues W e :=
  isoOfLinearEquiv e
    (fun f x => by simp only [transportValues, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply])
    (fun f x => by simp only [transportValues, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply])

theorem transportValues_isSimple (hM : M.IsSimple) :
    (M.transportValues W e).IsSimple := by
  constructor
  · obtain ⟨P, x, hx⟩ := hM.1
    refine ⟨P, e P x, ?_⟩
    intro hz
    apply hx
    exact (e P).injective (hz.trans (map_zero _).symm)
  · intro N
    let pre : M.Subfunctor :=
      { obj P := (N.obj P).comap (e P).toLinearMap
        pull_closed := by
          intro P Q f x hx
          have h := N.pull_closed f hx
          simpa [transportValues] using h
        push_closed := by
          intro P Q f x hx
          have h := N.push_closed f hx
          simpa [transportValues] using h }
    rcases hM.2 pre with hbot | htop
    · left
      intro P
      apply bot_unique
      intro x hx
      have hp : (e P).symm x ∈ pre.obj P := by
        change e P ((e P).symm x) ∈ N.obj P
        simpa using hx
      rw [hbot P] at hp
      have hx0 := congrArg (e P) hp
      simpa using hx0
    · right
      intro P
      apply top_unique
      intro x _
      have hp : (e P).symm x ∈ pre.obj P := by rw [htop P]; trivial
      change e P ((e P).symm x) ∈ N.obj P at hp
      simpa using hp

end Sharpness.MackeyModule

namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (hM : M.IsSimple) (Q : Subgroup S) (hQ : F.IsMinimalSupport M Q)

include hM hQ

/-- The actual finite direct sum (a dependent finitely supported family). -/
def DiazParkSimpleDirectSum (U : Subgroup S) : Type u :=
  Π₀ c : F.SimpleConjugacyClass Q U,
    LinearMap.range (F.simpleTransportedTrace M Q U (F.simpleClassRepresentative c))

instance (U : Subgroup S) : AddCommGroup (F.DiazParkSimpleDirectSum M Q U) :=
  inferInstanceAs (AddCommGroup (Π₀ c : F.SimpleConjugacyClass Q U,
    LinearMap.range (F.simpleTransportedTrace M Q U (F.simpleClassRepresentative c))))

instance (U : Subgroup S) : Module k (F.DiazParkSimpleDirectSum M Q U) :=
  inferInstanceAs (Module k (Π₀ c : F.SimpleConjugacyClass Q U,
    LinearMap.range (F.simpleTransportedTrace M Q U (F.simpleClassRepresentative c))))

def simpleDiazParkDirectSumEquiv (U : Subgroup S) :
    M.Value (F.toOrbit.obj ⟨U⟩) ≃ₗ[k] F.DiazParkSimpleDirectSum M Q U := by
  letI : Fintype (F.SimpleConjugacyClass Q U) := Fintype.ofFinite _
  exact (F.simpleDiazParkEquiv M Q U hM hQ).trans
    (DFinsupp.linearEquivFunOnFintype (R := k)).symm

/-- The simple functor attached to the given minimal module, with the
literal trace-image values of Díaz–Park formula (4). Its Mackey maps are
transported across the proved restriction-coordinate equivalences. -/
def simpleFunctorAtMinimal : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape :=
  M.transportValues (fun P => F.DiazParkSimpleDirectSum M Q P.as.subgroup)
    (fun P => F.simpleDiazParkDirectSumEquiv M hM Q hQ P.as.subgroup)

/-- An isomorphism of full Mackey functors, hence compatible with actual
restrictions, transfers and all fusion conjugation maps. -/
def simpleFunctorAtMinimalIso : M ≅ F.simpleFunctorAtMinimal M hM Q hQ :=
  M.transportValuesIso (fun P => F.DiazParkSimpleDirectSum M Q P.as.subgroup)
    (fun P => F.simpleDiazParkDirectSumEquiv M hM Q hQ P.as.subgroup)

theorem simpleFunctorAtMinimal_isSimple :
    (F.simpleFunctorAtMinimal M hM Q hQ).IsSimple :=
  M.transportValues_isSimple _ _ hM

def simpleSummandInjection (U : Subgroup S) (c : F.SimpleConjugacyClass Q U) :
    F.simpleTraceSummand M Q U c →ₗ[k] M.Value (F.toOrbit.obj ⟨U⟩) := by
  classical
  exact (F.simpleTraceEquiv M hM Q hQ U).symm.toLinearMap.comp
    (LinearMap.single k (fun d => F.simpleTraceSummand M Q U d) c)

/-- Formula (6) for a chosen minimal representative: the restriction
of its own summand is the inclusion of the trace image. -/
theorem simple_own_summand_restriction (U : Subgroup S)
    (c : F.SimpleConjugacyClass Q U) (x : F.simpleTraceSummand M Q U c) :
    M.pull (F.minimalInclusion (F.simpleClassRepresentative c))
      (F.simpleSummandInjection M hM Q hQ U c x) = x.val := by
  classical
  change ((F.simpleTraceEquiv M hM Q hQ U
    ((F.simpleTraceEquiv M hM Q hQ U).symm
      (LinearMap.single k (fun d => F.simpleTraceSummand M Q U d) c x))) c).val = _
  rw [LinearEquiv.apply_symm_apply]
  change ((Pi.single c x : (d : F.SimpleConjugacyClass Q U) →
    F.simpleTraceSummand M Q U d) c).val = x.val
  rw [Pi.single_eq_same]

/-- Formula (6) for all other chosen classes: their restriction is zero. -/
theorem simple_other_summand_restriction (U : Subgroup S)
    (c d : F.SimpleConjugacyClass Q U) (hcd : c ≠ d)
    (x : F.simpleTraceSummand M Q U d) :
    M.pull (F.minimalInclusion (F.simpleClassRepresentative c))
      (F.simpleSummandInjection M hM Q hQ U d x) = 0 := by
  classical
  change ((F.simpleTraceEquiv M hM Q hQ U
    ((F.simpleTraceEquiv M hM Q hQ U).symm
      (LinearMap.single k (fun c => F.simpleTraceSummand M Q U c) d x))) c).val = 0
  rw [LinearEquiv.apply_symm_apply]
  change ((Pi.single d x : (c : F.SimpleConjugacyClass Q U) →
    F.simpleTraceSummand M Q U c) c).val = 0
  rw [Pi.single_eq_of_ne hcd]
  rfl

theorem simple_own_summand_restriction_injective (U : Subgroup S)
    (c : F.SimpleConjugacyClass Q U) :
    Function.Injective (fun x : F.simpleTraceSummand M Q U c =>
      M.pull (F.minimalInclusion (F.simpleClassRepresentative c))
        (F.simpleSummandInjection M hM Q hQ U c x)) := by
  intro x y h
  apply Subtype.ext
  simpa only [F.simple_own_summand_restriction M hM Q hQ] using h

/-- Every element is the finite sum of these actual summands, with the
empty-index case included. -/
theorem simple_summand_sum (U : Subgroup S)
    (x : M.Value (F.toOrbit.obj ⟨U⟩)) :
    letI : Fintype (F.SimpleConjugacyClass Q U) := Fintype.ofFinite _
    (∑ c, F.simpleSummandInjection M hM Q hQ U c
      (F.simpleTraceEquiv M hM Q hQ U x c)) = x := by
  classical
  letI : Fintype (F.SimpleConjugacyClass Q U) := Fintype.ofFinite _
  apply (F.simpleTraceEquiv M hM Q hQ U).injective
  rw [map_sum]
  simp only [simpleSummandInjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  change (∑ c, (Pi.single c (F.simpleTraceEquiv M hM Q hQ U x c) :
    (d : F.SimpleConjugacyClass Q U) → F.simpleTraceSummand M Q U d)) = _
  exact LinearMap.sum_single_apply (fun d => F.simpleTraceSummand M Q U d)
    (F.simpleTraceEquiv M hM Q hQ U x)

end Sharpness.FusionSystem
