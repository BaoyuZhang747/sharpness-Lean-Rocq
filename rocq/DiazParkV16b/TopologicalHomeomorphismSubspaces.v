(** Restriction of actual homeomorphisms and flattening actual intersection subtypes. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology subtype_topology initial_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological.
Local Open Scope classical_set_scope.

Module DPTopologicalHomeomorphismSubspaces.
Section Restriction.
Variables X Y : topologicalType.
Variable e : homeomorphism X Y.
Variables (U : set X) (V : set Y).
Variable hUV : forall x, U x <-> V (iso_hom e x).
Let US := [the topologicalType of set_type U].
Let VS := [the topologicalType of set_type V].
Definition restricted_forward (x : US) : VS :=
  exist _ (iso_hom e (val x)) (mem_set ((hUV (val x)).1 (set_valP x))).
Lemma restricted_inverse_mem (y : VS) : U (iso_inv e (val y)).
Proof. apply/(hUV _).2; rewrite homeomorphism_inverseK; exact: set_valP. Qed.
Definition restricted_inverse (y : VS) : US :=
  exist _ (iso_inv e (val y)) (mem_set (restricted_inverse_mem y)).
Lemma restricted_forwardK : cancel restricted_forward restricted_inverse.
Proof. move=> x; apply: val_inj; exact: homeomorphism_forwardK. Qed.
Lemma restricted_inverseK : cancel restricted_inverse restricted_forward.
Proof. move=> y; apply: val_inj; exact: homeomorphism_inverseK. Qed.
Lemma restricted_forward_continuous : continuous restricted_forward.
Proof.
apply: (@continuous_comp_initial _ US Y set_val).
move=> x; apply: (@continuous_comp US X Y set_val (iso_hom e) x);
  [exact: initial_continuous | exact: cts_fun].
Qed.
Lemma restricted_inverse_continuous : continuous restricted_inverse.
Proof.
apply: (@continuous_comp_initial _ VS X set_val).
move=> y; apply: (@continuous_comp VS Y X set_val (iso_inv e) y);
  [exact: initial_continuous | exact: cts_fun].
Qed.
Definition restricted_homeomorphism : homeomorphism US VS :=
  homeomorphism_of_inverse restricted_forward_continuous restricted_inverse_continuous
    restricted_forwardK restricted_inverseK.
Lemma restricted_homeomorphism_val x : val (iso_hom restricted_homeomorphism x) = iso_hom e (val x).
Proof. reflexivity. Qed.
End Restriction.

Section Intersection.
Variable X : topologicalType.
Variables A B : set X.
Definition intersection_space := [the topologicalType of set_type (A `&` B)].
Definition intersection_nested_set : set [the topologicalType of set_type A] := fun a => B (val a).
Definition intersection_nested_space := [the topologicalType of set_type intersection_nested_set].

Definition intersection_to_nested (x : intersection_space) : intersection_nested_space.
Proof.
refine (exist _ (exist _ (val x) (mem_set (proj1 (set_valP x)))) _).
apply/mem_set; exact: (proj2 (set_valP x)).
Defined.
Definition intersection_from_nested (x : intersection_nested_space) : intersection_space :=
  exist _ (val (val x)) (mem_set (conj (set_valP (val x)) (set_valP x))).
Lemma intersection_to_nestedK : cancel intersection_to_nested intersection_from_nested.
Proof. move=> x; apply: val_inj; reflexivity. Qed.
Lemma intersection_from_nestedK : cancel intersection_from_nested intersection_to_nested.
Proof. move=> x; apply: val_inj; apply: val_inj; reflexivity. Qed.
Lemma intersection_to_nested_continuous : continuous intersection_to_nested.
Proof.
apply: (@continuous_comp_initial _ intersection_space [the topologicalType of set_type A] set_val).
apply: (@continuous_comp_initial _ intersection_space X set_val).
exact: initial_continuous.
Qed.
Lemma intersection_from_nested_continuous : continuous intersection_from_nested.
Proof.
apply: (@continuous_comp_initial _ intersection_nested_space X set_val).
move=> x; apply: (@continuous_comp _ [the topologicalType of set_type A] X set_val set_val x);
  exact: initial_continuous.
Qed.
Definition intersection_nested_homeomorphism : homeomorphism intersection_space intersection_nested_space :=
  homeomorphism_of_inverse intersection_to_nested_continuous intersection_from_nested_continuous
    intersection_to_nestedK intersection_from_nestedK.
Lemma intersection_nested_homeomorphism_val x :
  val (val (iso_hom intersection_nested_homeomorphism x)) = val x.
Proof. reflexivity. Qed.
End Intersection.
End DPTopologicalHomeomorphismSubspaces.
