(** The actual forgetful pullback map agrees with the canonical ordinary E3
    limit comparison after the native-to-Ran natural transformation. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits CategoryModuleLimitFunctor
  CategoryStructured CategoryComma HomologicalDiagramLimits HomologicalModuleIso
  FusionSystems FusionSaturation FusionCentralizerCover FusionCentralizerCoverProjection.
From DiazParkV16b Require Import LinkingSystem CategoryNerve SingularCohomology
  GeometricRealizationCarrier GeometricRealizationMaps GroupClassifyingCohomology.
From DiazParkV28 Require Import FusionCentralizerComma RightKanCohomology.
From DiazParkV29 Require Import MainSubgroup.
From DiazParkBLO Require Import BLODiagram BLOCohomologyNative BLOCohomologyComma
  BLOCohomologyMap BLOE3Limits BLOEdgeNativeCone BLOEdgeCoordinates.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCategoryNerve DPSingularCohomology DPGeometricRealization
  DPGeometricRealizationMaps DPGroupClassifyingCohomology DiazParkHomologicalModuleIso
  DPFusionCentralizerCoverProjection DPBLODiagram.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPBLOEdgeRanSquare.
Section Square.
Variable Real : realType.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis pS : p.-group [set: S].
Hypothesis ntS : [set: S] :!=: 1%G.
Hypothesis sat : DPFusionSaturation.saturated F p.
Local Notation K := [the fieldType of 'F_p].
Local Notation R := [the comPzRingType of (K : Type)].
Local Notation A := [the lmodType K of K^o].
Local Notation EC := (elementary_category F p).
Local Notation tau := (DPV28CentralizerComma.tau F p).
Local Notation nativeK := (@DPBLOCohomologyNative.native_coefficient Real S F L p R A).
Local Notation nativeForward := (@DPBLOCohomologyMap.native_ran_trans Real S F L p R A).
Local Notation forgetfulMap := (@DPBLOEdgeNativeCone.native_forgetful_limit_map Real S F L p R A).
Local Notation ambientEdge := (@DPV29LinkingSubgroup.native_edge_iso Real S F L p pS sat K (pchar_Fp hp) A).
Local Notation e3Limit := (@DPBLOE3Limits.ambient_to_ran_limit_iso S F p pS ntS sat).

Definition canonical_ran_edge n := module_iso_comp (ambientEdge n) (e3Limit n).

Theorem native_forward_forgetful_comma n z (E : EC)
    (X : structured_category tau E) :
  module_limit_val
    (@DPBLOCohomologyMap.native_to_ran Real S F L p R A n E
      (module_limit_val (module_hom_fun (forgetfulMap n) z) E)) X =
  module_limit_val (module_limit_val
    (module_hom_fun (iso_hom (e3Limit n))
      (module_hom_fun (iso_hom (ambientEdge n)) z)) E) X.
Proof.
rewrite DPBLOCohomologyMap.native_to_ran_coordinate
  DPBLOEdgeNativeCone.native_forgetful_limit_component.
rewrite /DPBLOCohomologyComma.comma_distinguished.
rewrite DPBLOEdgeCoordinates.distinguished_forgetful_square.
rewrite DPBLOE3Limits.ambient_to_ran_comma_value.
rewrite DPV29LinkingSubgroup.native_edge_component.
reflexivity.
Qed.

Theorem native_forward_forgetful_square n z :
  limit_action (nativeForward n) (module_hom_fun (forgetfulMap n) z) =
  module_hom_fun (iso_hom (canonical_ran_edge n)) z.
Proof.
apply module_limit_val_injective; apply functional_extensionality_dep => E.
rewrite limit_action_coordinate.
apply module_limit_val_injective; apply functional_extensionality_dep => X.
exact: native_forward_forgetful_comma.
Qed.
End Square.
End DPBLOEdgeRanSquare.
