From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness
  CategoryModuleLinear CategoryModuleProducts ModuleFiniteProducts ModuleInfrastructure MackeyModuleCarriers
  FusionSystems FusionOrbit FusionSaturation FusionMackeyShape
  MackeyStructures MackeyPair MackeyFusionMinimal.
From DiazParkV29 Require Import SimpleFunctor SimpleCentralizerSummands
  SimpleConjugacyIndices SimpleTraceSummands SimpleTraceDecomposition SimpleTransportedTrace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPFusionMackey.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPSimpleManuscript.
(** The literal trace image on M(Q), before or after the representative
    choice, vanishes.  Both bridges use the proved trace-image isomorphism. *)
Theorem transported_trace_summand_zero
    (S : finGroupType) (F : DPFusionSystem.system S) (R : comPzRingType)
    (M : mackey_module R (fusion_mackey_shape F)) (Q L U : {group S})
    (alpha : @isomorphism (orbit_category F) Q L) (hLU : L \subset U)
    (p : nat) (charp : p%:R = (0 : R)) (pU : p.-group U)
    (noncentric : ~~ (U :&: 'C(L) \subset L))
    (v : @DPSimpleTransportedTrace.transported_trace_summand S F R M Q L U alpha) : v = 0.
Proof.
pose e := @DPSimpleTransportedTrace.transported_trace_iso S F R M Q L U alpha.
apply: (@module_iso_hom_injective R _ _ e).
rewrite module_hom_zero.
exact: (@DPSimpleTraceSummands.centralizer_trace_summand_zero S F R (pair_of_mackey M)
  L U hLU p charp pU noncentric).
Qed.

Theorem represented_transported_trace_summand_zero
    (S : finGroupType) (F : DPFusionSystem.system S) (R : comPzRingType)
    (M : mackey_module R (fusion_mackey_shape F)) (simpleM : mackey_simple M)
    (Q : {group S}) (minimalQ : DPMackeyMinimal.subgroup_minimal M Q)
    (L U : {group S}) (hLU : L \subset U) (hQL : DPFusionSystem.conjugate F Q L)
    (p : nat) (charp : p%:R = (0 : R)) (pU : p.-group U)
    (noncentric : ~~ (U :&: 'C(L) \subset L))
    (v : @DPSimpleTransportedTrace.transported_trace_summand S F R M Q
      (DPSimpleConjugacyIndices.representative_subgroup
        (@DPSimpleCentralizerSummands.class_L S F Q L U hLU hQL)) U
      (DPSimpleFunctor.alpha (@DPSimpleCentralizerSummands.class_L S F Q L U hLU hQL))) : v = 0.
Proof.
pose i := @DPSimpleCentralizerSummands.class_L S F Q L U hLU hQL.
pose e := @DPSimpleTransportedTrace.transported_trace_iso S F R M Q
  (DPSimpleConjugacyIndices.representative_subgroup i) U (DPSimpleFunctor.alpha i).
apply: (@module_iso_hom_injective R _ _ e).
rewrite module_hom_zero.
exact: (@DPSimpleCentralizerSummands.represented_trace_summand_zero
  S F R M simpleM Q minimalQ L U hLU hQL p charp pU noncentric).
Qed.

Theorem simple_functor_centralizer_restriction_zero
    (S : finGroupType) (F : DPFusionSystem.system S) (R : comPzRingType)
    (M : mackey_module R (fusion_mackey_shape F)) (simpleM : mackey_simple M)
    (Q : {group S}) (minimalQ : DPMackeyMinimal.subgroup_minimal M Q)
    (L U : {group S}) (hLU : L \subset U) (hQL : DPFusionSystem.conjugate F Q L)
    (p : nat) (charp : p%:R = (0 : R)) (pU : p.-group U)
    (noncentric : ~~ (U :&: 'C(L) \subset L)) (x : mackey_value M U) :
    mackey_pull M (orbit_class (inclusion_arrow F hLU)) x = 0.
Proof.
pose i := @DPSimpleCentralizerSummands.class_L S F Q L U hLU hQL.
rewrite (@DPSimpleTraceDecomposition.summand_expansion S F R M simpleM Q minimalQ U x) linear_sum.
apply: big1=> j _.
case hj : (j == i).
- move/eqP: hj=> ->.
  pose e := @DPSimpleTransportedTrace.transported_trace_iso S F R M Q
    (DPSimpleConjugacyIndices.representative_subgroup i) U (DPSimpleFunctor.alpha i).
  pose v := @DPSimpleTraceDecomposition.coordinates S F R M simpleM Q minimalQ U x i.
  have hz := @represented_transported_trace_summand_zero S F R M simpleM Q minimalQ
    L U hLU hQL p charp pU noncentric (module_hom_fun (iso_inv e) v).
  have hv : v = 0.
    rewrite -[v](module_iso_inv_hom_apply e v) hz; exact: module_hom_zero.
  change (mackey_pull M (orbit_class (inclusion_arrow F hLU))
    (@DPSimpleTraceDecomposition.summand_embedding S F R M simpleM Q minimalQ U i v) = 0).
  by rewrite hv /DPSimpleTraceDecomposition.summand_embedding !linear0.
- apply: (@DPSimpleCentralizerSummands.restriction_other_class
    S F R M simpleM Q minimalQ L U hLU hQL j) => he.
  by move: hj; rewrite he eqxx.
Qed.

(** Exact manuscript specialisations: saturation occurs in part (iii),
    while the stronger construction and detection theorem require none. *)
Theorem lemma_2_8_ii (S : finGroupType) (F : DPFusionSystem.system S)
    (p : nat) (M : mackey_module [the fieldType of 'F_p] (fusion_mackey_shape F))
    (simpleM : mackey_simple M) (Q : {group S})
    (minimalQ : DPMackeyMinimal.subgroup_minimal M Q) (U : {group S})
    (x : mackey_value M U) :
    (forall (L : {group S}) (hLU : L \subset U), DPFusionSystem.conjugate F Q L ->
      mackey_pull M (orbit_class (inclusion_arrow F hLU)) x = 0) -> x = 0.
Proof. exact: (@DPSimpleFunctor.simple_functor_restriction_detection S F _ M simpleM Q minimalQ U x). Qed.

Theorem lemma_2_8_iii (S : finGroupType) (F : DPFusionSystem.system S)
    (p : nat) (primep : prime p) (pS : p.-group [set: S])
    (saturatedF : DPFusionSaturation.saturated F p)
    (M : mackey_module [the fieldType of 'F_p] (fusion_mackey_shape F))
    (simpleM : mackey_simple M) (Q : {group S})
    (minimalQ : DPMackeyMinimal.subgroup_minimal M Q)
    (L U : {group S}) (hLU : L \subset U) (hQL : DPFusionSystem.conjugate F Q L)
    (noncentric : ~~ (U :&: 'C(L) \subset L)) (x : mackey_value M U) :
    mackey_pull M (orbit_class (inclusion_arrow F hLU)) x = 0.
Proof.
exact: (@simple_functor_centralizer_restriction_zero S F _ M simpleM Q minimalQ L U hLU hQL
  p (pcharf0 (pchar_Fp primep)) (pgroupS (subsetT U) pS) noncentric x).
Qed.
End DPSimpleManuscript.

Print Assumptions DPSimpleFunctor.simple_functor_identification.
Print Assumptions DPSimpleFunctor.S_Q_MQ_simple.
Print Assumptions DPSimpleFunctor.simple_functor_restriction_detection.
Print Assumptions DPSimpleCentralizerSummands.represented_trace_summand_zero.
Print Assumptions DPSimpleManuscript.simple_functor_centralizer_restriction_zero.
Print Assumptions DPSimpleManuscript.lemma_2_8_ii.
Print Assumptions DPSimpleManuscript.lemma_2_8_iii.
