(** The genuine topological attaching quotient, for arbitrary continuous maps. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical topology
  sigT_topology quotient_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope quotient_scope.
Local Open Scope classical_set_scope.

Module DPTopologicalPushoutCarrier.
Import DPTopological.

Lemma native_quotient_eq (T : choiceType) (e : equiv_rel T) (p q : T) :
  (\pi_{eq_quot e} p : {eq_quot e}) = \pi_{eq_quot e} q <-> e p q.
Proof.
have h := @eqmodP T e p q.
split; [exact: introT h | exact: elimT h].
Qed.

Section Carrier.
Variables A B X : topologicalType.
Variables (i : hom topological_category A B) (j : hom topological_category A X).

Definition attaching_index := [the choiceType of {classic bool}].
Definition attaching_family (side : attaching_index) : topologicalType := if side then B else X.
Definition attaching_raw := {side : attaching_index & attaching_family side}.
Definition attaching_raw_space : topologicalType :=
  [the topologicalType of {side : attaching_index & attaching_family side}].
Definition raw_left (b : B) : attaching_raw := existT attaching_family true b.
Definition raw_right (x : X) : attaching_raw := existT attaching_family false x.

Lemma raw_left_continuous : continuous (raw_left : B -> attaching_raw_space).
Proof. exact: (@existT_continuous attaching_index attaching_family true). Qed.
Lemma raw_right_continuous : continuous (raw_right : X -> attaching_raw_space).
Proof. exact: (@existT_continuous attaching_index attaching_family false). Qed.

Definition raw_left_map : continuousType B attaching_raw_space :=
  @continuous_map B attaching_raw_space raw_left raw_left_continuous.
Definition raw_right_map : continuousType X attaching_raw_space :=
  @continuous_map X attaching_raw_space raw_right raw_right_continuous.

Lemma raw_left_composite_continuous (Q : topologicalType) (q : attaching_raw_space -> Q)
  (hq : continuous q) : continuous (q \o raw_left).
Proof.
move=> b; apply: (@continuous_comp _ attaching_raw_space Q raw_left q b);
  [exact: raw_left_continuous | exact: hq].
Qed.
Lemma raw_right_composite_continuous (Q : topologicalType) (q : attaching_raw_space -> Q)
  (hq : continuous q) : continuous (q \o raw_right).
Proof.
move=> x; apply: (@continuous_comp _ attaching_raw_space Q raw_right q x);
  [exact: raw_right_continuous | exact: hq].
Qed.

Inductive attaching_equivalent : attaching_raw -> attaching_raw -> Prop :=
| attaching_refl p : attaching_equivalent p p
| attaching_sym p q : attaching_equivalent p q -> attaching_equivalent q p
| attaching_trans p q r : attaching_equivalent p q ->
    attaching_equivalent q r -> attaching_equivalent p r
| attaching_glue a : attaching_equivalent (raw_left (i a)) (raw_right (j a)).

Definition attaching_related (p q : attaching_raw) := `[< attaching_equivalent p q >].
Lemma attaching_related_refl : reflexive attaching_related.
Proof. move=> p; apply/asboolP; exact: attaching_refl. Qed.
Lemma attaching_related_sym : symmetric attaching_related.
Proof. move=> p q; apply/idP/idP => /asboolP h; apply/asboolP; exact: attaching_sym h. Qed.
Lemma attaching_related_trans : transitive attaching_related.
Proof. move=> p q r /asboolP h /asboolP k; apply/asboolP; exact: attaching_trans h k. Qed.
Definition attaching_equiv := EquivRel attaching_related attaching_related_refl
  attaching_related_sym attaching_related_trans.
Definition attaching_quotient := {eq_quot attaching_equiv}.
Definition attaching := quotient_topology [the quotType attaching_raw of attaching_quotient].
Definition attaching_space : topologicalType :=
  [the topologicalType of quotient_topology [the quotType attaching_raw of attaching_quotient]].
Definition attaching_class (p : attaching_raw) : attaching := \pi_attaching p.

Lemma attaching_class_eq p q :
  attaching_class p = attaching_class q <-> attaching_equivalent p q.
Proof.
change ((\pi_attaching_quotient p : attaching_quotient) = \pi_attaching_quotient q <-> attaching_equivalent p q).
rewrite native_quotient_eq.
split; [by move/asboolP | by move=> h; apply/asboolP].
Qed.

Lemma attaching_class_surjective z : exists p, attaching_class p = z.
Proof. exists (repr z); exact: reprK. Qed.
Lemma attaching_class_continuous : continuous attaching_class.
Proof. exact: pi_continuous. Qed.

Local Opaque attaching_equiv attaching_quotient.

Definition attaching_class_map : continuousType attaching_raw_space attaching_space :=
  @continuous_map attaching_raw_space attaching_space attaching_class attaching_class_continuous.
Definition attaching_left_map : hom topological_category B attaching_space :=
  @continuous_compose B attaching_raw_space attaching_space raw_left_map attaching_class_map.
Definition attaching_right_map : hom topological_category X attaching_space :=
  @continuous_compose X attaching_raw_space attaching_space raw_right_map attaching_class_map.
Definition attaching_left (b : B) : attaching := attaching_class (raw_left b).
Definition attaching_right (x : X) : attaching := attaching_class (raw_right x).
Definition attaching_left_continuous :=
  @raw_left_composite_continuous attaching_space attaching_class attaching_class_continuous.
Definition attaching_right_continuous :=
  @raw_right_composite_continuous attaching_space attaching_class attaching_class_continuous.

Lemma attaching_commutes : compose i attaching_left_map = compose j attaching_right_map.
Proof. apply: topological_hom_ext => a; apply/attaching_class_eq; exact: attaching_glue. Qed.

Lemma attaching_cases (z : attaching_space) :
  (exists b, attaching_left b = z) \/ (exists x, attaching_right x = z).
Proof.
have [[[] y] <-] := attaching_class_surjective z.
- left; by exists y.
- right; by exists y.
Qed.

Lemma attaching_open_iff (U : set attaching_space) :
  open U <-> open (attaching_left @^-1` U) /\ open (attaching_right @^-1` U).
Proof.
change (open (attaching_class @^-1` U) <-> open (attaching_left @^-1` U) /\ open (attaching_right @^-1` U)).
rewrite sigT_openP; split.
- move=> h; split; [exact: (h true) | exact: (h false)].
- move=> [hB hX] []; [exact: hB | exact: hX].
Qed.

Lemma attaching_closed_iff (U : set attaching_space) :
  closed U <-> closed (attaching_left @^-1` U) /\ closed (attaching_right @^-1` U).
Proof.
rewrite -!openC.
exact: attaching_open_iff.
Qed.

End Carrier.
End DPTopologicalPushoutCarrier.
