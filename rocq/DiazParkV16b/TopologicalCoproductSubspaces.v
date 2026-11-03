(** Native sum topology commutes with taking a family of actual subspaces. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology
  sigT_topology subtype_topology initial_topology unstable.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCoproductHomotopy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalCoproductHomotopy.
Local Open Scope classical_set_scope.

Module DPTopologicalCoproductSubspaces.
Section Family.
Variable I : choiceType.
Variable X : I -> topologicalType.
Variable U : forall i, set (X i).
Arguments U i : clear implicits.

Definition family_subspaces := family_space (fun i => [the topologicalType of set_type (U i)]).
Definition family_subset : set (family_space X) := fun z => U (projT1 z) (projT2 z).
Definition family_subspace := [the topologicalType of set_type family_subset].

Definition family_subspaces_to (z : family_subspaces) : family_subspace :=
  exist _ (existT X (projT1 z) (val (projT2 z))) (mem_set (set_valP (projT2 z))).
Definition family_subspaces_from (z : family_subspace) : family_subspaces :=
  existT (fun i => [the topologicalType of set_type (U i)]) (projT1 (val z))
    (exist _ (projT2 (val z)) (mem_set (set_valP z))).

Lemma family_subspaces_toK : cancel family_subspaces_to family_subspaces_from.
Proof.
move=> [i [x hx]]; rewrite /family_subspaces_to /family_subspaces_from /=.
congr (existT (fun i => [the topologicalType of set_type (U i)]) i _).
apply: val_inj; reflexivity.
Qed.
Lemma family_subspaces_fromK : cancel family_subspaces_from family_subspaces_to.
Proof. move=> [[i x] hx]; apply: val_inj; reflexivity. Qed.

Lemma family_subspaces_to_continuous : continuous family_subspaces_to.
Proof.
apply: (@continuous_comp_initial _ family_subspaces _ set_val).
apply: (@sigT_continuous I (fun i => [the topologicalType of set_type (U i)]) (family_space X)
  (fun i x => existT X i (val x))).
move=> i x; apply: (@continuous_comp _ (X i) (family_space X) set_val (existT X i) x);
  [exact: initial_continuous | exact: existT_continuous].
Qed.

Lemma family_subspaces_from_continuous : continuous family_subspaces_from.
Proof.
apply/continuousP => W hW.
have hWi i : @open [the topologicalType of set_type (U i)]
    (existT (fun i => [the topologicalType of set_type (U i)]) i @^-1` W) :=
  (proj1 (sigT_openP W) hW) i.
have hO i : exists O : set (X i), open O /\
    forall x : set_type (U i), W (existT (fun i => [the topologicalType of set_type (U i)]) i x) <-> O (val x).
  have [O hO e] := hWi i.
  exists O; split=> // x.
  change ((existT (fun i => [the topologicalType of set_type (U i)]) i @^-1` W) x <->
    (set_val @^-1` O) x).
  rewrite -e; reflexivity.
pose O i := get [set V : set (X i) | open V /\
  forall x : set_type (U i), W (existT (fun i => [the topologicalType of set_type (U i)]) i x) <-> V (val x)].
have hOi i : open (O i) /\ forall x : set_type (U i),
    W (existT (fun i => [the topologicalType of set_type (U i)]) i x) <-> O i (val x).
  exact: getPex (hO i).
pose V : set (family_space X) := fun z => O (projT1 z) (projT2 z).
have hV : open V.
  apply/sigT_openP => i; exact: (proj1 (hOi i)).
exists V => //.
apply/seteqP; split=> z hz.
- apply (proj2 (hOi (projT1 (val z))) (exist _ (projT2 (val z)) (mem_set (set_valP z)))).2.
  exact hz.
- apply (proj2 (hOi (projT1 (val z))) (exist _ (projT2 (val z)) (mem_set (set_valP z)))).1.
  exact hz.
Qed.

Definition family_subspaces_homeomorphism : homeomorphism family_subspaces family_subspace :=
  homeomorphism_of_inverse family_subspaces_to_continuous family_subspaces_from_continuous
    family_subspaces_toK family_subspaces_fromK.

Lemma family_subspaces_homeomorphism_val z :
  val (iso_hom family_subspaces_homeomorphism z) =
    existT X (projT1 z) (val (projT2 z)).
Proof. reflexivity. Qed.

Lemma family_subset_open (hU : forall i, open (U i)) : open family_subset.
Proof. apply/sigT_openP => i; exact: hU. Qed.
Lemma family_subset_closed (hU : forall i, closed (U i)) : closed family_subset.
Proof.
rewrite -openC; apply/sigT_openP => i.
change (open (~` (U i))); by rewrite openC.
Qed.

End Family.
End DPTopologicalCoproductSubspaces.
