import Sharpness.GroupCohomologyFunctorData

/-! From the general raw restriction/transfer formula to a full Mackey
object on the actual orbit category, with native ordinary cohomology
values and native group-homomorphism pullbacks. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators
variable {S R : Type u} [Group S] [Finite S] [CommRing R] (F : FusionSystem S)
    {A : Type u} [AddCommGroup A] [Module R A]
    {n : ℕ} (I : F.GroupCohomologyTransferLaws (R := R) A n)

theorem groupCohomologyFunctorData_raw_identity
    {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T) :
    ((F.groupCohomologyFunctorData I).pull (F.toOrbit.map f)).comp
      ((F.groupCohomologyFunctorData I).push (F.toOrbit.map g)) =
      ∑ i : F.RawDoubleCosetTerm f g,
        F.functorDataDoubleCosetOperator (F.groupCohomologyFunctorData I) f g i := by
  change (F.groupCohomologyOrbitPull (F.toOrbit.map f)).comp
    (F.groupCohomologyOrbitPush I (F.toOrbit.map g)) = _
  rw [F.groupCohomologyOrbitPull_raw I, F.groupCohomologyOrbitPush_raw I]
  apply (I.double_coset f g).trans
  apply Finset.sum_congr rfl
  intro i _
  rw [F.functorDataDoubleCosetOperator_out]
  change (F.groupCohomologyRawPush I.transfer (F.concreteSpan f g i.out).left).comp
      (F.groupCohomologyRawPull (F.concreteSpan f g i.out).right n) =
    (F.groupCohomologyOrbitPush I (F.toOrbit.map (F.concreteSpan f g i.out).left)).comp
      (F.groupCohomologyOrbitPull (F.toOrbit.map (F.concreteSpan f g i.out).right))
  rw [F.groupCohomologyOrbitPush_raw I, F.groupCohomologyOrbitPull_raw I]
  rfl

def groupCohomologyMackey : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape :=
  F.fullMackeyOfRawIdentity (F.groupCohomologyFunctorData I)
    (F.groupCohomologyFunctorData_raw_identity I)

theorem groupCohomologyMackey_pull_raw {P Q : F.Object} (f : P ⟶ Q) :
    (F.groupCohomologyMackey I).pull (F.toOrbit.map f) =
      OrdinaryCohomology.pullLinear (R := R) (A := A) f.val n :=
  F.groupCohomologyOrbitPull_raw I f

theorem groupCohomologyMackey_push_raw {P Q : F.Object} (f : P ⟶ Q) :
    (F.groupCohomologyMackey I).push (F.toOrbit.map f) =
      (I.transfer (F.imageSubgroup f) Q.subgroup (F.image_le f)).comp
        (OrdinaryCohomology.pullLinear (R := R) (A := A) (F.imageIso f).inv.val n) :=
  F.groupCohomologyOrbitPush_raw I f

end Sharpness.FusionSystem
