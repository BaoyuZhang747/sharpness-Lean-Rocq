From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  CategoryModuleExactness HomologicalModuleIso ModuleInfrastructure MackeyModuleCarriers
  FusionMaps FusionSystems FusionConjugacy FusionOrbit FusionOrbitRanks FusionMackeyShape
  MackeyStructures MackeyPair TraceNormalizerAction TraceNormalizerCosets
  FusionOuterAutomorphisms FusionOuterEndomorphisms.
From DiazParkV29 Require Import SimpleTraceSummands.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPFusionMackey DPNormalizerAction DPSimpleTraceSummands.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Module DPSimpleTransportedTrace.
Section Transport.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_module R (fusion_mackey_shape F).
Variables Q L U : {group S}.
Variable alpha : @isomorphism (orbit_category F) Q L.
Let forward := mackey_push M (iso_hom alpha).
Let backward := mackey_push M (iso_inv alpha).

Lemma transport_cancel x : backward (forward x) = x.
Proof. exact: mackey_push_iso_cancel. Qed.
Lemma transport_cancel_back x : forward (backward x) = x.
Proof. exact (@mackey_push_iso_cancel R (orbit_category F) (fusion_mackey_shape F) M L Q (iso_symm alpha) x). Qed.

(** This is precisely the conjugated action alpha^{-1} gamma alpha on
    the original minimal value M(Q), written in the native right-action
    convention.  Normalizer classes are actual orbit endomorphisms. *)
Definition transported_action (v : mackey_value M Q) (q : coset_of L) :=
  backward (@quotient_action S F R (pair_of_mackey M) L (forward v) q).
Lemma transported_action_arrow v q :
  transported_action v q =
  mackey_push M (compose (compose (iso_hom alpha) (quotient_class F q)) (iso_inv alpha)) v.
Proof. by rewrite /transported_action !mackey_push_comp. Qed.
Lemma transported_action_one v : transported_action v (1%g : coset_of L) = v.
Proof. by rewrite /transported_action quotient_action_one transport_cancel. Qed.
Lemma transported_action_mul v a b :
  transported_action (transported_action v a) b = transported_action v (a * b)%g.
Proof.
rewrite /transported_action transport_cancel_back quotient_action_mul.
reflexivity.
Qed.
Lemma transported_action_outer v q :
  transported_action v q =
  mackey_push M (@DPFusionOuterEndomorphisms.outer_endomorphism S F Q
    (@DPFusionOuterEndomorphisms.endomorphism_outer S F Q
      (compose (compose (iso_hom alpha) (quotient_class F q)) (iso_inv alpha)))) v.
Proof. by rewrite DPFusionOuterEndomorphisms.endomorphism_outerK transported_action_arrow. Qed.

Definition transported_trace (v : mackey_value M Q) :=
  \sum_(q in (trace_normalizer L U / L)%g) transported_action v q.
Lemma transported_trace_linear : linear transported_trace.
Proof.
move=> a x y; rewrite /transported_trace scaler_sumr -big_split /=.
apply: eq_bigr=> q _; by rewrite /transported_action /quotient_action !linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R (mackey_value M Q)
  (mackey_value M Q) _ transported_trace transported_trace_linear.

Lemma transported_trace_intertwines v :
  forward (transported_trace v) =
  @normalizer_trace S F R (pair_of_mackey M) L U (forward v).
Proof.
rewrite /transported_trace linear_sum /normalizer_trace.
apply: eq_bigr=> q _; exact: transport_cancel_back.
Qed.

Definition transported_trace_image := linear_image (transported_trace : {linear _ -> _}).
Definition transported_trace_summand : lmodType R :=
  [the lmodType R of submodule_carrier transported_trace_image].

Lemma image_forward v : transported_trace_image v ->
  trace_image (pair_of_mackey M) L U (forward v).
Proof. move=> [x <-]; exists (forward x); symmetry; exact: transported_trace_intertwines. Qed.
Definition trace_transport (v : transported_trace_summand) : trace_summand (pair_of_mackey M) L U :=
  submodule_in (image_forward (submodule_val_mem v)).
Lemma trace_transport_val v : submodule_val (trace_transport v) = forward (submodule_val v).
Proof. reflexivity. Qed.
Lemma trace_transport_linear : linear trace_transport.
Proof.
move=> a x y; apply: submodule_val_injective.
change (forward (a *: submodule_val x + submodule_val y) =
  a *: forward (submodule_val x) + forward (submodule_val y)).
exact: linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R transported_trace_summand
  (trace_summand (pair_of_mackey M) L U) _ trace_transport trace_transport_linear.

Lemma trace_transport_injective : injective trace_transport.
Proof.
move=> x y h; apply: submodule_val_injective.
apply: (@mackey_push_iso_injective R (orbit_category F) (fusion_mackey_shape F) M Q L alpha).
exact (congr1 (@submodule_val R (mackey_value M L) (trace_image (pair_of_mackey M) L U)) h).
Qed.
Lemma trace_transport_surjective : forall w, exists v, trace_transport v = w.
Proof.
move=> w; have [x hx] := trace_image_mem w.
have hv : transported_trace_image (transported_trace (backward x)) by exists (backward x).
exists (submodule_in hv); apply: submodule_val_injective.
rewrite trace_transport_val /= transported_trace_intertwines transport_cancel_back.
exact hx.
Qed.
Definition transported_trace_iso :
  @isomorphism (module_category R) transported_trace_summand (trace_summand (pair_of_mackey M) L U) :=
  DiazParkHomologicalModuleIso.linear_bijection_iso trace_transport_injective trace_transport_surjective.
End Transport.

Section FusionChoice.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables Q L : {group S}.
Hypothesis hQL : DPFusionSystem.conjugate F Q L.
Lemma fusion_transport_exists : exists e : @isomorphism (orbit_category F) Q L, True.
Proof.
move/existsP: hQL=> [f /andP[hf /eqP onto]].
exists (@DPFusionRanks.raw_onto_iso S F Q L (Sub f hf) onto); exact I.
Qed.
Definition fusion_transport := proj1_sig (constructive_indefinite_description fusion_transport_exists).
End FusionChoice.
End DPSimpleTransportedTrace.
