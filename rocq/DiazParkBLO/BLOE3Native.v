(** Closed BLO-03 endpoints for the actual native enlarged-category coefficient.
    The native-to-Ran comparison is constructed in BLO-02 and instantiated
    here; it is not a hypothesis. The raw double-opposite singular coefficient
    is also covered for the actual replacement-edge construction. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp
  all_classical reals topology.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryModules CategoryModuleExactness CategoryDerivedLimits CategoryDerivedIsomorphism
  HomologicalModuleIso FusionSystems FusionSaturation FusionCentralizerCoverProjection.
From DiazParkV16b Require Import LinkingSystem SingularCochainReplacementEdge.
From DiazParkV28 Require Import CategoryFiberRanComparison RightKanCohomology.
From DiazParkBLO Require Import BLOCohomologyNative BLOCohomology BLODiagramNerve BLOE3Transport.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DPFusionCentralizerCoverProjection
  DPSingularReplacementEdge.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPBLOE3Native.
Section Native.
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

Section Degree.
Variable n : nat.
Local Notation native := (@DPBLOCohomology.native_coefficient Real S F L p n).
Local Notation raw := (@DPBLOCohomologyNative.raw_coefficient Real S F L p R A n).

Definition native_higher_limit_comparison (s : nat) : @isomorphism (module_category K)
  (derived_limit K native s)
  (derived_limit K (@DPV28RightKanCohomology.ambient_cohomology S F p n) s) :=
  @DPBLOE3Transport.higher_limit_comparison S F p hp pS sat n ntS native
    (@DPBLOCohomology.native_ran_nat_iso Real S F L p hp pS sat n) s.

Theorem native_positive_higher_limits_zero (s : nat) (hs : (0 < s)%N) :
  forall v : derived_limit K native s, v = 0.
Proof.
exact (@DPBLOE3Transport.positive_higher_limits_zero S F p hp pS sat n ntS native
  (@DPBLOCohomology.native_ran_nat_iso Real S F L p hp pS sat n) s hs).
Qed.

Definition raw_higher_limit_comparison (s : nat) : @isomorphism (module_category K)
  (derived_limit K raw s)
  (derived_limit K (@DPV28RightKanCohomology.ambient_cohomology S F p n) s) :=
  module_iso_comp (nat_iso_component (derived_category_iso_nat_iso K
    (DPV28FiberRanComparison.double_opposite_iso EC) s) raw)
    (native_higher_limit_comparison s).

Theorem raw_positive_higher_limits_zero (s : nat) (hs : (0 < s)%N) :
  forall v : derived_limit K raw s, v = 0.
Proof.
pose e := nat_iso_component (derived_category_iso_nat_iso K
  (DPV28FiberRanComparison.double_opposite_iso EC) s) raw.
intro v; apply (@module_iso_hom_injective K _ _ e).
rewrite module_hom_zero; exact (@native_positive_higher_limits_zero s hs _).
Qed.
End Degree.

Theorem raw_positive_limits_vanish :
  singular_positive_limits_vanish Real A (@DPBLODiagramNerve.space_diagram S F L p Real).
Proof.
move=> n j v.
exact (@raw_positive_higher_limits_zero n j.+1 (ltn0Sn j) v).
Qed.
End Native.
End DPBLOE3Native.
