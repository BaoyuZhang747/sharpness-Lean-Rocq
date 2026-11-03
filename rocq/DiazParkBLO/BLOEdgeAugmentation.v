(** The actual enlarged-category cocone induces a native singular cochain
    augmentation. No sharpness or augmentation quasi-isomorphism is assumed. *)
From mathcomp Require Import all_boot all_algebra all_fingroup all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  FusionSystems FusionCentralizerCoverProjection.
From DiazParkV16b Require Import LinkingSystem TopologicalCategory SingularCohomology
  CategoryNerve SimplicialReplacementConstants GeometricRealizationCarrier
  GeometricRealizationMaps SingularCochainReplacementEdge.
From DiazParkBLO Require Import BLODiagram BLODiagramNerve BLOEdgeComparison.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularCohomology DPCategoryNerve
  DPGeometricRealization DPGeometricRealizationMaps DPSingularReplacementEdge
  DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DPFusionCentralizerCoverProjection DPBLODiagram DPBLODiagramNerve.

Module DPBLOEdgeAugmentation.
Section Diagram.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Local Notation I := (opposite (elementary_category F p)).
Local Notation D := (@space_diagram S F L p Real).
Local Notation Y := (realization_space Real (nerve (DPCentricLinking.linking_category L))).
Local Notation a := (@space_forgetful S F L p Real).

(** The raw singular coefficient is contravariant on I, hence has literal
    domain opposite(opposite(F^e)). The final K_n uses the explicit double-op
    isomorphism to the covariant F^e convention. *)
Definition raw_coefficient n : module_codiagram R I :=
  singular_cohomology_diagram Real A D n.

Definition replacement_total := singular_replacement_total Real A D.

Definition cochain_augmentation : cochain_map (singular_cochains Real Y A)
    replacement_total :=
  @DPBLOEdgeComparison.augmentation Real R A I D Y a.

Theorem cochain_augmentation_component n z (E : elementary_object F p) :
  cochain_map_at (singular_replacement_projection Real A D E) n
    (cochain_map_at cochain_augmentation n z) =
  cochain_map_at (singular_pullback Real
    (realization_map Real (nerve_map (forgetful L (val E)))) A) n z.
Proof. exact: DPBLOEdgeComparison.augmentation_cochain_component. Qed.

Theorem cohomology_augmentation_component n z (E : elementary_object F p) :
  cohomology_map (singular_replacement_projection Real A D E) n
    (cohomology_map cochain_augmentation n z) =
  singular_cohomology_map Real
    (realization_map Real (nerve_map (forgetful L (val E)))) A n z.
Proof. exact: DPBLOEdgeComparison.augmentation_cohomology_component. Qed.

Definition raw_positive_limits_vanish : Prop :=
  singular_positive_limits_vanish Real A D.

Definition raw_edge (hD : raw_positive_limits_vanish) n
    (z : singular_cohomology Real Y A n) :=
  @DPBLOEdgeComparison.edge Real R A I D Y a hD n z.
Arguments raw_edge hD n z : clear implicits.

Theorem raw_edge_component (hD : raw_positive_limits_vanish) n z
    (E : elementary_object F p) :
  module_limit_val (raw_edge hD n z) E =
  singular_cohomology_map Real
    (realization_map Real (nerve_map (forgetful L (val E)))) A n z.
Proof. exact: DPBLOEdgeComparison.edge_component. Qed.
End Diagram.
End DPBLOEdgeAugmentation.
