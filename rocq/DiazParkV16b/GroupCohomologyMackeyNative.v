(** Unconditional native ordinary group cohomology as a full Mackey module on
    the actual fusion orbit category, with its canonical double-coset shape. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules MackeyStructures MackeyPair
  MackeyFusionBridge MackeyBarReduction MackeyDiagramIdentities
  FusionMaps FusionSystems FusionOrbit FusionMackeyShape.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyOrbitCoefficient
  GroupCohomologyMackeyPushBase GroupCohomologyMackeyPair GroupCohomologyMackeyDiagram
  GroupCohomologyMackeyDoubleCosetShape.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomologyOrbitCoefficient DPGroupCohomologyMackeyPushBase
  DPGroupCohomologyMackeyPair DPGroupCohomologyMackeyDiagram
  DPGroupCohomologyMackeyDoubleCosetShape.

Module DPGroupCohomologyMackeyNative.
Section Native.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.

Definition native_cohomology_mackey :
    mackey_module R (DPFusionMackey.fusion_mackey_shape F) :=
  @DPMackeyFusion.full_mackey_of_inclusions S F R (native_cohomology_pair F A n)
    (@native_inclusion_mackey_formula S F R A n).

Theorem native_mackey_value (P : {group S}) :
  mackey_value native_cohomology_mackey P =
    DPGroupCohomology.value R [the finGroupType of [subg P]] A n.
Proof. reflexivity. Qed.

Theorem native_mackey_pull (P Q : {group S}) (a : DPFusionSystem.arrow F P Q) z :
  mackey_pull native_cohomology_mackey (DPFusionOrbit.orbit_class a) z =
    module_hom_fun (raw_pull A n a) z.
Proof. exact: native_pair_pull_class. Qed.

Theorem native_mackey_push (P Q : {group S}) (a : DPFusionSystem.arrow F P Q) z :
  mackey_push native_cohomology_mackey (DPFusionOrbit.orbit_class a) z =
    module_hom_fun (raw_push A n a) z.
Proof. exact: native_pair_push_class. Qed.

Theorem native_mackey_centric_diagram :
  mackey_codiagram (DPFusionOrbit.centric_inclusion F) native_cohomology_mackey =
    centric_coefficient F A n.
Proof.
rewrite /native_cohomology_mackey /DPMackeyFusion.full_mackey_of_inclusions
  of_pair_codiagram; exact: native_centric_pair_codiagram.
Qed.

End Native.
End DPGroupCohomologyMackeyNative.
