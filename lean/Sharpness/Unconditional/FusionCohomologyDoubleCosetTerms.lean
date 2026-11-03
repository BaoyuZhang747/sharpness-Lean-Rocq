import Sharpness.Unconditional.FusionCohomologyDoubleCosetSpans
import Sharpness.Manuscript.CohomologyFunctorData
import Sharpness.Unconditional.GroupCohomologyMackeyCohomology

/-! Actual pullbacks on the intersection charts and literal native
cohomology expressions for the concrete fusion span operators. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory OrdinaryCohomology
open scoped BigOperators
variable {S R A : Type u} [Group S] [Finite S] [CommRing R]
    [AddCommGroup A] [Module R A] (F : FusionSystem S)
    {P Q T : F.Object} (hP : P.subgroup ≤ T.subgroup) (hQ : Q.subgroup ≤ T.subgroup)

theorem inclusionNativeConjugation_comp_symm (x : T.subgroup) :
    (F.inclusionNativeConjugation (P := P) (Q := Q) x).comp
      (F.inclusionNativeIntersectionEquiv hP hQ x).symm.toMonoidHom =
    (F.concreteSpan (F.inclusion hP) (F.inclusion hQ) x⁻¹).right.val := by
  rw [← F.inclusionNativeIntersectionEquiv_right hP hQ x]
  ext y
  change ((F.concreteSpan (F.inclusion hP) (F.inclusion hQ) x⁻¹).right.val
    ((F.inclusionNativeIntersectionEquiv hP hQ x)
      ((F.inclusionNativeIntersectionEquiv hP hQ x).symm y)) : S) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The charted conjugation is literally the native Mackey conjugation
followed by the canonical removal of Q's subgroup-of-T wrapper. -/
theorem inclusionNativeConjugation_eq (x : T.subgroup) :
    F.inclusionNativeConjugation (P := P) (Q := Q) x =
      (Subgroup.subgroupOfEquivOfLe hQ).toMonoidHom.comp
        (MackeyDecomposition.intersectionConjugation
          (Q.subgroup.subgroupOf T.subgroup) (P.subgroup.subgroupOf T.subgroup) x) := by
  ext y
  rfl

/-- The native pullback along the actual fusion right leg in intersection coordinates. -/
theorem inclusionSpan_rawPull_native (x : T.subgroup) (n : ℕ) :
    F.groupCohomologyRawPull (R := R) (A := A)
      (F.concreteSpan (F.inclusion hP) (F.inclusion hQ) x⁻¹).right n =
    (pullLinear (F.inclusionNativeIntersectionEquiv hP hQ x).symm.toMonoidHom n).comp
      (pullLinear (F.inclusionNativeConjugation (P := P) (Q := Q) x) n) := by
  change pullLinear _ n = _
  rw [← F.inclusionNativeConjugation_comp_symm hP hQ x, pullLinear_comp]

/-- The left raw push is the actual literal-subgroup transfer. -/
theorem inclusionSpan_rawPush_native (x : T.subgroup) (n : ℕ) :
    F.groupCohomologyRawPush
      (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n)
      (F.concreteSpan (F.inclusion hP) (F.inclusion hQ) x⁻¹).left =
    subgroupTransfer (F.spanApex (F.inclusion hP) (F.inclusion hQ) x⁻¹).subgroup
      P.subgroup (lifted_le _ _) n :=
  F.nativeGroupCohomologyRawPush_inclusion _ n

variable (n : ℕ)
    (hcomp : ∀ {P Q T : F.Object} (f : P ⟶ Q) (g : Q ⟶ T),
      F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (A := A) n) (f ≫ g) =
        (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) g).comp
          (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) f))

/-- Native functor data use exactly the raw concrete-span maps, with no
Mackey assumption in the intermediate functor data. -/
theorem cohomologyFunctorDataOfPush_span_raw {P Q T : F.Object}
    (f : P ⟶ T) (g : Q ⟶ T) (x : T.subgroup) :
    F.functorDataSpanOperator (F.cohomologyFunctorDataOfPush n hcomp) f g x =
      (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (A := A) n)
        (F.concreteSpan f g x).left).comp
          (F.groupCohomologyRawPull (F.concreteSpan f g x).right n) := by
  change ((F.cohomologyFunctorDataOfPush n hcomp).push
      (F.toOrbit.map (F.concreteSpan f g x).left)).comp
    ((F.cohomologyFunctorDataOfPush n hcomp).pull
      (F.toOrbit.map (F.concreteSpan f g x).right)) = _
  rw [F.cohomologyFunctorDataOfPush_push_raw, F.cohomologyFunctorDataOfPush_pull_raw]

/-- Every actual span term is expressed using the native conjugation pullback
and literal native subgroup transfer through the proved intersection chart. -/
theorem cohomologyFunctorDataOfPush_inclusionSpan (x : T.subgroup) :
    F.functorDataSpanOperator (F.cohomologyFunctorDataOfPush n hcomp)
      (F.inclusion hP) (F.inclusion hQ) x⁻¹ =
    (subgroupTransfer
      (F.spanApex (F.inclusion hP) (F.inclusion hQ) x⁻¹).subgroup P.subgroup
      (lifted_le _ _) n).comp
        ((pullLinear (F.inclusionNativeIntersectionEquiv hP hQ x).symm.toMonoidHom n).comp
          (pullLinear (F.inclusionNativeConjugation (P := P) (Q := Q) x) n)) := by
  rw [F.cohomologyFunctorDataOfPush_span_raw,
    F.inclusionSpan_rawPush_native, F.inclusionSpan_rawPull_native]

end Sharpness.FusionSystem
