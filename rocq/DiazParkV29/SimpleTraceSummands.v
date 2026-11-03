From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup center pgroup.
From DiazPark Require Import Category ModuleInfrastructure MackeyModuleCarriers
  FusionMaps FusionSystems FusionOrbit FusionMackeyShape MackeyStructures MackeyPair
  MackeyFusionBridge TraceNormalizerCosets TraceNormalizerAction
  TraceMackeyQuotient TraceCentralizerZero TraceCentralizerIndex TraceCosets.

(** The summands in Diaz--Park formula (4) are images of the actual
    normalizer trace, not arbitrary copies of a minimal value. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPFusionMackey DPNormalizerAction.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPSimpleTraceSummands.
Section TraceImages.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_pair R (orbit_category F).

Definition normalizer_trace (L U : {group S}) (x : pair_value M L) :=
  \sum_(q in (trace_normalizer L U / L)%g) @quotient_action S F R M L x q.

Lemma normalizer_trace_linear L U : linear (@normalizer_trace L U).
Proof.
move=> a x y; rewrite /normalizer_trace scaler_sumr -big_split /=.
apply: eq_bigr=> q _; exact: linearP.
Qed.
HB.instance Definition _ L U := GRing.isLinear.Build R (pair_value M L)
  (pair_value M L) _ (@normalizer_trace L U) (@normalizer_trace_linear L U).

Definition trace_image (L U : {group S}) : module_subspace (pair_value M L) :=
  linear_image (@normalizer_trace L U : {linear _ -> _}).
Definition trace_summand (L U : {group S}) : lmodType R :=
  [the lmodType R of submodule_carrier (trace_image L U)].

Lemma trace_image_mem L U (v : trace_summand L U) :
  exists x : pair_value M L, normalizer_trace U x = submodule_val v.
Proof. exact (@submodule_val_mem R (pair_value M L) (trace_image L U) v). Qed.

Lemma self_restriction_is_trace (L U : {group S}) (hLU : L \subset U)
    (minimal : forall A : {group S}, (#|A| < #|L|)%N ->
      forall x : pair_value M A, x = 0)
    (hM : DPMackeyFusion.inclusion_mackey_formula M) (x : pair_value M L) :
    pair_pull M (orbit_class (inclusion_arrow F hLU))
      (pair_push M (orbit_class (inclusion_arrow F hLU)) x) = normalizer_trace U x.
Proof. exact: self_trace_quotient. Qed.

(** The intermediate subgroup is L C_U(L), with the genuine quotient
    inclusion into N_U(L)/L.  Its action is trivial because the actual
    orbit action kills inner automorphisms. *)
Lemma centralizer_intermediate_action_trivial (L U : {group S})
    (q : coset_of L) (hq : q \in (DPTraceCentralizer.product L U / L)%g)
    (v : pair_value M L) : @quotient_action S F R M L v q = v.
Proof. exact (@DPCentralizerTrace.centralizer_product_quotient_trivial S F R M L U q hq v). Qed.

Lemma intermediate_trace_is_index (L U : {group S}) (v : pair_value M L) :
    \sum_(q in (DPTraceCentralizer.product L U / L)%g)
       @quotient_action S F R M L v q =
    v *+ #|(DPTraceCentralizer.product L U / L)%g|.
Proof.
rewrite -sumr_const; apply: eq_bigr=> q hq.
exact (@centralizer_intermediate_action_trivial L U q hq v).
Qed.

Lemma centralizer_trace_image_zero (L U : {group S}) (hLU : L \subset U)
    (p : nat) (charp : p%:R = (0 : R)) (pU : p.-group U)
    (noncentric : ~~ (U :&: 'C(L) \subset L)) :
    forall x, trace_image L U x -> x = 0.
Proof.
move=> x [v <-].
exact: (@DPCentralizerTrace.quotient_trace_zero S F R M L U p charp hLU pU noncentric v).
Qed.

Theorem centralizer_trace_summand_zero (L U : {group S}) (hLU : L \subset U)
    (p : nat) (charp : p%:R = (0 : R)) (pU : p.-group U)
    (noncentric : ~~ (U :&: 'C(L) \subset L)) (v : trace_summand L U) : v = 0.
Proof.
apply: submodule_val_injective.
change (submodule_val v = 0).
exact: (centralizer_trace_image_zero hLU charp pU noncentric (submodule_val_mem v)).
Qed.
End TraceImages.
End DPSimpleTraceSummands.
