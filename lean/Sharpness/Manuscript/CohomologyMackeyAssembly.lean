import Sharpness.Manuscript.CohomologyFunctorData
import Sharpness.Unconditional.InclusionMackeyBridge

/-! The final assembly step for native group-cohomology transfers. Arbitrary
fusion-map Mackey identities follow from the inclusion identities once the
actual raw push maps are proved functorial. Both intermediate premises are
explicit here; the unconditional constructor instantiates them separately. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators
variable {S R A : Type u} [Group S] [Finite S] [CommRing R]
    [AddCommGroup A] [Module R A] (F : FusionSystem S) (n : ℕ)
    (hcomp : ∀ {P Q T : F.Object} (f : P ⟶ Q) (g : Q ⟶ T),
      F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (A := A) n) (f ≫ g) =
        (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) g).comp
          (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) f))

theorem nativeCohomology_double_coset_of_inclusions
    (identity : F.HasInclusionMackeyFormula (F.cohomologyFunctorDataOfPush n hcomp))
    {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T) :
    (F.groupCohomologyRawPull (R := R) (A := A) f n).comp
        (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) g) =
      ∑ i : F.RawDoubleCosetTerm f g,
        (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n)
          (F.concreteSpan f g i.out).left).comp
            (F.groupCohomologyRawPull (F.concreteSpan f g i.out).right n) := by
  have h := F.rawMackeyFormula_of_inclusions
    (F.cohomologyFunctorDataOfPush n hcomp) identity f g
  rw [F.cohomologyFunctorDataOfPush_pull_raw,
    F.cohomologyFunctorDataOfPush_push_raw] at h
  refine h.trans (Finset.sum_congr rfl (fun i _ => ?_))
  rw [F.functorDataDoubleCosetOperator_out]
  change ((F.cohomologyFunctorDataOfPush n hcomp).push
      (F.toOrbit.map (F.concreteSpan f g i.out).left)).comp
        ((F.cohomologyFunctorDataOfPush n hcomp).pull
          (F.toOrbit.map (F.concreteSpan f g i.out).right)) = _
  rw [F.cohomologyFunctorDataOfPush_push_raw,
    F.cohomologyFunctorDataOfPush_pull_raw]
  rfl

/-- An assembly lemma, with functoriality and inclusion Mackey identities
explicitly supplied. The resulting record uses the constructed native transfer. -/
def cohomologyTransferLawsOfInclusions
    (identity : F.HasInclusionMackeyFormula (F.cohomologyFunctorDataOfPush n hcomp)) :
    F.GroupCohomologyTransferLaws (R := R) A n where
  transfer := nativeGroupCohomologyTransfer n
  inner := F.cohomologyRawPull_inner_unconditional n
  transfer_comp := hcomp
  transfer_iso e := F.nativeGroupCohomologyRawPush_iso e n
  double_coset := F.nativeCohomology_double_coset_of_inclusions n hcomp identity

end Sharpness.FusionSystem
