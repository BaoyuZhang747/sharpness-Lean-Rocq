(** Closed native BLO centraliser cohomological sharpness. The natural
    comparison, positive limits and canonical map square are proved inputs,
    not hypotheses. This asserts a mod-p cochain quasi-isomorphism and the
    actual all-degree forgetful edge, not a full homotopy equivalence. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp
  all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  CategoryModuleLimitFunctor CategoryModuleExactness CategoryDerivedLimits
  HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
  HomologicalDiagramLimits MackeyModuleCarriers MackeyModuleQuotient
  FusionSystems FusionSaturation FusionCentralizerCoverProjection.
From DiazParkV16b Require Import LinkingSystem CategoryNerve SingularCohomology
  GeometricRealizationCarrier GeometricRealizationMaps SingularCochainReplacementEdge.
From DiazParkBLO Require Import BLODiagram BLODiagramNerve BLOCohomology
  BLOCohomologyMap BLOE3Native BLOEdgeComparison BLOEdgeAugmentation
  BLOEdgeVariance BLOEdgeNativeCone BLOEdgeRanSquare.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCategoryNerve DPSingularCohomology DPGeometricRealization
  DPGeometricRealizationMaps DPSingularReplacementEdge DiazParkCohomology
  DiazParkCohomologyMaps DiazParkHomologicalModuleIso
  DPFusionCentralizerCoverProjection DPBLODiagram.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPBLOEdgeFinal.
Section Sharpness.
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
Local Notation I := (opposite EC).
Local Notation D := (@DPBLODiagramNerve.space_diagram S F L p Real).
Local Notation Y := (realization_space Real (nerve (DPCentricLinking.linking_category L))).
Local Notation a := (@DPBLODiagramNerve.space_forgetful S F L p Real).
Local Notation nativeK := (@DPBLOCohomology.native_coefficient Real S F L p).
Local Notation nativeForward := (@DPBLOCohomologyMap.native_ran_trans Real S F L p R A).
Local Notation forgetfulMap := (@DPBLOEdgeNativeCone.native_forgetful_limit_map Real S F L p R A).
Local Notation nativeComparison := (@DPBLOCohomology.native_ran_nat_iso Real S F L p hp pS sat).
Local Notation canonicalRanEdge := (@DPBLOEdgeRanSquare.canonical_ran_edge Real S F L p hp pS ntS sat).
Local Notation variance := (@DPBLOEdgeNativeCone.variance_iso Real S F L p R A).
Local Notation rawPositive := (@DPBLOE3Native.raw_positive_limits_vanish Real S F L p hp pS ntS sat).
Local Notation actualAugmentation := (@DPBLOEdgeAugmentation.cochain_augmentation S F L p Real R A).

Definition native_limit_iso n :=
  functor_iso (module_limit_functor K EC) (nativeComparison n).

Lemma native_limit_iso_forward n x :
  module_hom_fun (iso_hom (native_limit_iso n)) x = limit_action (nativeForward n) x.
Proof.
change (limit_action (iso_hom (nativeComparison n)) x = limit_action (nativeForward n) x).
by rewrite DPBLOCohomology.native_ran_nat_iso_hom.
Qed.

Definition native_edge_iso n : @isomorphism (module_category K)
    [the lmodType K of singular_cohomology Real Y A n]
    (module_limit_type (nativeK n)) :=
  module_iso_comp (canonicalRanEdge n) (iso_symm (native_limit_iso n)).

Theorem native_edge_iso_forward n z :
  module_hom_fun (iso_hom (native_edge_iso n)) z =
  module_hom_fun (forgetfulMap n) z.
Proof.
apply (module_iso_hom_injective (e := native_limit_iso n)).
change (module_hom_fun (iso_hom (native_limit_iso n))
  (module_hom_fun (iso_inv (native_limit_iso n))
    (module_hom_fun (iso_hom (canonicalRanEdge n)) z)) =
  module_hom_fun (iso_hom (native_limit_iso n)) (module_hom_fun (forgetfulMap n) z)).
rewrite module_iso_inv_hom_apply native_limit_iso_forward.
symmetry; exact: DPBLOEdgeRanSquare.native_forward_forgetful_square.
Qed.

Theorem native_edge_component n z (E : EC) :
  module_limit_val (module_hom_fun (iso_hom (native_edge_iso n)) z) E =
  singular_cohomology_map Real
    (realization_map Real (nerve_map (forgetful L (val E)))) A n z.
Proof.
rewrite native_edge_iso_forward.
exact: DPBLOEdgeNativeCone.native_forgetful_limit_component.
Qed.

Definition raw_edge_iso n := module_iso_comp (native_edge_iso n) (iso_symm (variance n)).

Theorem raw_edge_iso_component n z (E : EC) :
  module_limit_val (module_hom_fun (iso_hom (raw_edge_iso n)) z) E =
  singular_cohomology_map Real (component a E) A n z.
Proof.
change (module_limit_val (module_hom_fun (iso_inv (variance n))
  (module_hom_fun (iso_hom (native_edge_iso n)) z)) E =
  singular_cohomology_map Real (component a E) A n z).
rewrite DPBLOEdgeVariance.covariant_to_raw_component.
exact: native_edge_component.
Qed.

Definition augmentation_cohomology_iso n : @isomorphism (module_category K)
    [the lmodType K of singular_cohomology Real Y A n]
    (cohomology (singular_replacement_total Real A D) n) :=
  module_iso_comp (raw_edge_iso n) (iso_symm (singular_replacement_limit_iso rawPositive n)).

Theorem augmentation_cohomology_iso_forward n z :
  module_hom_fun (iso_hom (augmentation_cohomology_iso n)) z =
  cohomology_map actualAugmentation n z.
Proof.
exact (@DPBLOEdgeComparison.augmentation_cohomology_iso_hom
  Real R A I D Y a rawPositive (@raw_edge_iso) (@raw_edge_iso_component) n z).
Qed.

Theorem augmentation_cochain_quasi_isomorphism :
  forall n, bijective (cohomology_map actualAugmentation n).
Proof.
exact (@DPBLOEdgeComparison.augmentation_cochain_quasi_isomorphism
  Real R A I D Y a rawPositive (@raw_edge_iso) (@raw_edge_iso_component)).
Qed.

Theorem native_edge_is_actual_augmentation_edge n z :
  module_hom_fun (iso_hom (native_edge_iso n)) z =
  module_hom_fun (iso_hom (variance n))
    (module_hom_fun (iso_hom (singular_replacement_limit_iso rawPositive n))
      (cohomology_map actualAugmentation n z)).
Proof.
apply module_limit_val_injective; apply functional_extensionality_dep => E.
rewrite native_edge_component DPBLOEdgeVariance.raw_to_covariant_component
  singular_replacement_limit_iso_component.
symmetry; exact: DPBLOEdgeAugmentation.cohomology_augmentation_component.
Qed.

Theorem native_forgetful_limit_bijective n :
  bijective (module_hom_fun (forgetfulMap n)).
Proof.
exists (module_hom_fun (iso_inv (native_edge_iso n))).
- move=> z; rewrite -native_edge_iso_forward; exact: module_iso_hom_inv_apply.
- move=> z; rewrite -native_edge_iso_forward; exact: module_iso_inv_hom_apply.
Qed.

Theorem centralizer_cohomological_sharpness :
  (forall n s, (0 < s)%N -> forall v : derived_limit K (nativeK n) s, v = 0) /\
  (forall n, bijective (module_hom_fun (forgetfulMap n))).
Proof.
split.
- exact (@DPBLOE3Native.native_positive_higher_limits_zero Real S F L p hp pS ntS sat).
- exact: native_forgetful_limit_bijective.
Qed.
End Sharpness.
End DPBLOEdgeFinal.
