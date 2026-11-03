(** The simple-functor statements use an arbitrary inclusion-minimal
    subgroup, rather than a prescribed least-cardinality choice. *)
From mathcomp Require Import all_boot all_algebra all_fingroup center pgroup.
From DiazPark Require Import Category ModuleInfrastructure FusionMaps FusionSystems
  FusionOrbit FusionConjugacy FusionMackeyShape MackeyStructures MackeyPair
  MackeyFusionBridge MackeyFusionMinimal MackeyGroupAlgebraOuter MackeyGroupAlgebraSimple
  FusionMackeyFullBridge TraceGeneratedRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPFusionMackey.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPMackeyMinimalManuscript.
Section FullMackey.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_module R (fusion_mackey_shape F).
Hypothesis simpleM : mackey_simple M.
Variable Q : {group S}.
Hypothesis minimalQ : DPMackeyMinimal.subgroup_minimal M Q.

Theorem minimal_is_least : mackey_least_nonzero M (fun P : {group S} => #|P|) Q.
Proof.
have [Q0 leastQ0] := DPMackeyMinimal.least_nonzero_exists simpleM.1.
have hc := @DPMackeyMinimal.minimal_conjugate S F R M Q0 leastQ0 simpleM Q minimalQ.
exact (@DPMackeyMinimal.conjugate_least_nonzero S F R M Q0 leastQ0 Q hc).
Qed.

Theorem minimal_support_iff_conjugate (P : {group S}) :
    DPMackeyMinimal.subgroup_minimal M P <-> DPFusionSystem.conjugate F Q P.
Proof.
exact (@DPMackeyMinimal.minimal_support_iff_conjugate S F R M Q minimal_is_least simpleM P).
Qed.

Theorem minimal_outer_group_algebra_simple (L : {group S})
    (hQL : DPFusionSystem.conjugate F Q L) :
    module_is_simple (@DPMackeyOuterModule.outer_group_algebra_module S F R M L).
Proof.
exact (@DPMackeyOuterModule.conjugate_outer_group_algebra_simple
  S F R M L Q minimal_is_least simpleM hQL).
Qed.

Theorem minimal_inclusion_transfer_generation (U : {group S}) (x : mackey_value M U) :
    module_span (@DPMackeyMinimal.inclusion_transfer_generator S F R M Q U) x.
Proof.
exact (@DPMackeyMinimal.inclusion_transfer_generation S F R M Q minimal_is_least simpleM U x).
Qed.

Theorem minimal_inclusion_restriction_detection (U : {group S}) (x : mackey_value M U) :
    (forall (L : {group S}) (hLU : L \subset U), DPFusionSystem.conjugate F Q L ->
      mackey_pull M (orbit_class (inclusion_arrow F hLU)) x = 0) -> x = 0.
Proof.
exact (@DPMackeyMinimal.inclusion_restriction_detection S F R M Q minimal_is_least simpleM U x).
Qed.

Theorem minimal_inclusion_restriction_injective (U : {group S})
    (x y : mackey_value M U) :
    (forall (L : {group S}) (hLU : L \subset U), DPFusionSystem.conjugate F Q L ->
      mackey_pull M (orbit_class (inclusion_arrow F hLU)) x =
      mackey_pull M (orbit_class (inclusion_arrow F hLU)) y) -> x = y.
Proof.
exact (@DPMackeyMinimal.inclusion_restriction_injective S F R M Q minimal_is_least simpleM U x y).
Qed.

Theorem minimal_value_zero_without_conjugates (U : {group S})
    (h : forall (L : {group S}), L \subset U -> ~~ DPFusionSystem.conjugate F Q L)
    (x : mackey_value M U) : x = 0.
Proof.
apply: minimal_inclusion_restriction_detection => L hLU hc.
by move: (h L hLU); rewrite hc.
Qed.

Theorem minimal_centralizer_restriction_zero (L T : {group S})
    (hQL : DPFusionSystem.conjugate F Q L) (hLT : L \subset T)
    (p : nat) (charp : p%:R = (0 : R)) (pT : p.-group T)
    (noncentric : ~~ (T :&: 'C(L) \subset L)) (x : mackey_value M T) :
    mackey_pull M (orbit_class (inclusion_arrow F hLT)) x = 0.
Proof.
pose hM := @DPFusionMackeyFullBridge.full_inclusion_mackey S F R M.
have simpleP : mackey_simple (DPMackeyFusion.full_mackey_of_inclusions hM).
  by rewrite /hM DPFusionMackeyFullBridge.full_inclusion_roundtrip.
have leastP : mackey_least_nonzero (DPMackeyFusion.full_mackey_of_inclusions hM)
    (fun A : {group S} => #|A|) Q.
  rewrite /hM DPFusionMackeyFullBridge.full_inclusion_roundtrip; exact: minimal_is_least.
exact (@DPCentralizerRestriction.centralizer_restriction_zero S F R (pair_of_mackey M)
  hM simpleP Q leastP L T hQL hLT p charp pT noncentric x).
Qed.
End FullMackey.

Section PairedMackey.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_pair R (orbit_category F).
Hypothesis hM : DPMackeyFusion.inclusion_mackey_formula M.
Let full := DPMackeyFusion.full_mackey_of_inclusions hM.
Hypothesis simpleM : mackey_simple full.
Variable Q : {group S}.
Hypothesis minimalQ : DPMackeyMinimal.subgroup_minimal full Q.

Theorem inclusion_minimal_centralizer_restriction_zero (L T : {group S})
    (hQL : DPFusionSystem.conjugate F Q L) (hLT : L \subset T)
    (p : nat) (charp : p%:R = (0 : R)) (pT : p.-group T)
    (noncentric : ~~ (T :&: 'C(L) \subset L)) (x : pair_value M T) :
    pair_pull M (orbit_class (inclusion_arrow F hLT)) x = 0.
Proof.
exact (@DPCentralizerRestriction.centralizer_restriction_zero S F R M hM simpleM Q
  (@minimal_is_least S F R full simpleM Q minimalQ) L T hQL hLT p charp pT noncentric x).
Qed.
End PairedMackey.
End DPMackeyMinimalManuscript.

Check DPMackeyMinimalManuscript.minimal_is_least.
Check DPMackeyMinimalManuscript.minimal_support_iff_conjugate.
Check DPMackeyMinimalManuscript.minimal_outer_group_algebra_simple.
Check DPMackeyMinimalManuscript.minimal_inclusion_transfer_generation.
Check DPMackeyMinimalManuscript.minimal_inclusion_restriction_detection.
Check DPMackeyMinimalManuscript.minimal_centralizer_restriction_zero.
Print Assumptions DPMackeyMinimalManuscript.minimal_is_least.
Print Assumptions DPMackeyMinimalManuscript.minimal_outer_group_algebra_simple.
Print Assumptions DPMackeyMinimalManuscript.minimal_centralizer_restriction_zero.
