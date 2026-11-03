(** Actual complementary-open homeomorphism for a closed-injection attachment. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology subtype_topology initial_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory CategoryPushout
  TopologicalPushoutComparison TopologicalPushoutEmbedding TopologicalOpenBijection
  TopologicalCoproductSubspaceImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPCategoryPushout DPTopologicalPushoutComparison DPTopologicalPushoutEmbedding
  DPTopologicalOpenBijection DPTopologicalCoproductSubspaceImages.
Local Open Scope classical_set_scope.

Module DPTopologicalPushoutComplement.
Section Complement.
Variables A B X Y : topologicalType.
Variables (i : hom topological_category A B) (j : hom topological_category A X)
  (k : hom topological_category B Y) (l : hom topological_category X Y).
Variable h : pushout_square i j k l.
Variable hi : injective i.
Variable hi_closed : forall S : set A, closed S -> closed (i @` S).

Definition source_complement : set B := ~` (i @` [set: A]).
Definition target_complement : set Y := ~` (l @` [set: X]).
Definition source_complement_space := [the topologicalType of set_type source_complement].
Definition target_complement_space := [the topologicalType of set_type target_complement].

Lemma source_complement_open : open source_complement.
Proof. rewrite /source_complement openC; exact: hi_closed closedT. Qed.
Lemma target_complement_open : open target_complement.
Proof. rewrite /target_complement openC; exact: (pushout_right_closed_image h hi hi_closed closedT). Qed.

Lemma complement_image_mem (b : source_complement_space) : target_complement (k (val b)).
Proof.
move=> [x _ e].
have [a [ea _]] := (proj1 (pushout_left_right h hi (val b) x)) (esym e).
apply (set_valP b); by exists a.
Qed.

Definition complement_map_fun (b : source_complement_space) : target_complement_space :=
  exist _ (k (val b)) (mem_set (@complement_image_mem b)).

Lemma complement_map_continuous : continuous complement_map_fun.
Proof.
apply: (@continuous_comp_initial _ source_complement_space Y set_val).
move=> b; apply: (@continuous_comp _ B Y set_val k b);
  [exact: initial_continuous | exact: cts_fun].
Qed.
Definition complement_map : continuousType source_complement_space target_complement_space :=
  continuous_map complement_map_continuous.

Lemma complement_map_injective : injective complement_map.
Proof.
move=> b b' e; apply: val_inj.
have hb' : ~ exists a, i a = val b'.
  move=> [a ea]; apply (set_valP b'); by exists a.
apply (proj1 (pushout_left_outside_fibre h hi hb' (val b))).
exact (congr1 (@set_val _ target_complement) e).
Qed.

Lemma complement_map_surjective (y : target_complement_space) : exists b, complement_map b = y.
Proof.
case: (pushout_cases h (val y)) => [[b eb]|[x ex]].
- have hb : source_complement b.
    move=> [a _ ea]; apply (set_valP y); exists (j a); first by [].
    rewrite -eb -ea; symmetry.
    exact (congr1 (fun f : hom topological_category A Y => f a) (pushout_commutes h)).
  exists (exist _ b (mem_set hb)); apply: val_inj; exact eb.
- exfalso; apply (set_valP y); by exists x.
Qed.

Lemma complement_ambient_image_open (S : set source_complement_space) (hS : open S) :
  open (k @` (set_val @` S)).
Proof.
have hSB : open (set_val @` S : set B) := subtype_val_image_open source_complement_open hS.
apply/(pushout_open_iff h); split.
- have e : k @^-1` (k @` (set_val @` S)) = set_val @` S.
    apply/seteqP; split=> b.
    * move=> [b' [s hs es] ek].
      have hb' : ~ exists a, i a = b'.
        move=> [a ea]; apply (set_valP s); exists a; first by []; exact: etrans ea (esym es).
      have -> : b = b' := (proj1 (pushout_left_outside_fibre h hi hb' b)) (esym ek).
      by exists s.
    * move=> hb; by exists b.
  by rewrite e.
- have e : l @^-1` (k @` (set_val @` S)) = set0.
    apply/seteqP; split=> x; last by [].
    move=> [b [s hs es] ek].
    have [a [ea _]] := (proj1 (pushout_left_right h hi b x)) ek.
    apply (set_valP s); exists a; first by []; exact: etrans ea (esym es).
  by rewrite e; exact: open0.
Qed.

Lemma complement_map_open (S : set source_complement_space) (hS : open S) :
  open (complement_map @` S).
Proof.
have e : complement_map @` S = set_val @^-1` (k @` (set_val @` S)).
  apply/seteqP; split=> y.
  - move=> [b hb <-]; exists (val b); first by exists b.
    reflexivity.
  - move=> [b [s hs es] ek]. exists s; first exact hs.
    apply: val_inj; exact (etrans (congr1 k es) ek).
rewrite e; apply: open_comp; last exact: complement_ambient_image_open hS.
move=> y _; exact: initial_continuous.
Qed.

Definition pushout_complement_homeomorphism : homeomorphism source_complement_space target_complement_space :=
  @open_bijection_homeomorphism _ _ complement_map complement_map_injective
    complement_map_surjective complement_map_open.

Lemma pushout_complement_homeomorphism_val b :
  val (iso_hom pushout_complement_homeomorphism b) = k (val b).
Proof. reflexivity. Qed.
End Complement.
End DPTopologicalPushoutComplement.
