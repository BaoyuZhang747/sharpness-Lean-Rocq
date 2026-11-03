(** The canonical forgetful restriction map into the ordinary limit of the
    literal covariant elementary-category native coefficient. *)
From mathcomp Require Import all_boot all_algebra all_fingroup all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  MackeyModuleCarriers MackeyModuleQuotient FusionSystems FusionCentralizerCoverProjection.
From DiazParkV16b Require Import LinkingSystem CategoryNerve SingularCohomology
  GeometricRealizationCarrier GeometricRealizationMaps.
From DiazParkBLO Require Import BLODiagram BLOCohomologyNative BLOEdgeAugmentation
  BLOEdgeCone BLOEdgeVariance.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCategoryNerve DPSingularCohomology DPGeometricRealization
  DPGeometricRealizationMaps DPFusionCentralizerCoverProjection DPBLODiagram.

Module DPBLOEdgeNativeCone.
Section Native.
Variable Real : realType.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable R : comPzRingType.
Variable A : lmodType R.
Local Notation EC := (elementary_category F p).
Local Notation Y := (realization_space Real (nerve (DPCentricLinking.linking_category L))).
Local Notation rawK := (@DPBLOEdgeAugmentation.raw_coefficient S F L p Real R A).
Local Notation nativeK := (@DPBLOCohomologyNative.native_coefficient Real S F L p R A).

Definition variance_iso n : @isomorphism (module_category R)
    (module_limit_type (rawK n)) (module_limit_type (nativeK n)) :=
  @DPBLOEdgeVariance.raw_to_covariant_limit_iso R EC (rawK n).

Definition native_forgetful_limit_map n : module_hom
    [the lmodType R of singular_cohomology Real Y A n]
    (module_limit_type (nativeK n)) :=
  module_hom_comp (@DPBLOEdgeCone.forgetful_limit_map S F L p Real R A n)
    (iso_hom (variance_iso n)).

Theorem native_forgetful_limit_component n z (E : EC) :
  module_limit_val (module_hom_fun (native_forgetful_limit_map n) z) E =
  singular_cohomology_map Real
    (realization_map Real (nerve_map (forgetful L (val E)))) A n z.
Proof.
change (module_limit_val (module_hom_fun (iso_hom (variance_iso n))
  (module_hom_fun (@DPBLOEdgeCone.forgetful_limit_map S F L p Real R A n) z)) E =
  singular_cohomology_map Real
    (realization_map Real (nerve_map (forgetful L (val E)))) A n z).
rewrite DPBLOEdgeVariance.raw_to_covariant_component.
exact: DPBLOEdgeCone.forgetful_limit_component.
Qed.
End Native.
End DPBLOEdgeNativeCone.
