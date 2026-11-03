(** Genuine open/closed injection stability for arbitrary topological pushouts. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory CategoryPushout
  TopologicalPushoutCarrier TopologicalPushoutUniversal TopologicalPushoutFibres
  TopologicalPushoutComparison TopologicalPushoutSeparation.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module DPTopologicalPushoutEmbedding.
Import DPTopological DPCategoryPushout DPTopologicalPushoutCarrier
  DPTopologicalPushoutUniversal DPTopologicalPushoutFibres
  DPTopologicalPushoutComparison DPTopologicalPushoutSeparation.

Lemma injective_homeomorphism_leg {P Y X : topologicalType} (e : homeomorphism P Y)
  (f : X -> P) (l : X -> Y) (h : forall x, iso_hom e (f x) = l x)
  (hf : injective f) : injective l.
Proof.
move=> x y hx; apply hf; apply (@homeomorphism_injective P Y e).
by rewrite !h.
Qed.

Lemma homeomorphism_leg_equality {P Y B X : topologicalType} (e : homeomorphism P Y)
  (f : B -> P) (g : X -> P) (k : B -> Y) (l : X -> Y)
  (hf : forall b, iso_hom e (f b) = k b) (hg : forall x, iso_hom e (g x) = l x)
  (b : B) (x : X) : k b = l x <-> f b = g x.
Proof.
rewrite -hf -hg; split.
- exact: (@homeomorphism_injective P Y e).
- move=> ->; reflexivity.
Qed.

Lemma open_pushout_right_image {A B X Y : topologicalType}
  (i : hom topological_category A B) (j : hom topological_category A X)
  (k : hom topological_category B Y) (l : hom topological_category X Y)
  (hlinj : injective l)
  (hcross : forall b x, k b = l x <-> exists a, i a = b /\ j a = x)
  (hfinal : forall S : set Y, open S <-> open (k @^-1` S) /\ open (l @^-1` S))
  (hi_open : forall S : set A, open S -> open (i @` S))
  (S : set X) (hS : open S) : open (l @` S).
Proof.
apply/hfinal; split.
- rewrite (@closed_pushout_left_preimage_right_image A B X Y i j k l hcross).
  apply hi_open. have hc : continuous j by exact: cts_fun.
  exact ((proj1 (continuousP j) hc) S hS).
- by rewrite (@closed_pushout_right_preimage_image X Y l hlinj).
Qed.

Section Actual.
Variables A B X Y : topologicalType.
Variables (i : hom topological_category A B) (j : hom topological_category A X)
  (k : hom topological_category B Y) (l : hom topological_category X Y).
Variable h : pushout_square i j k l.
Variable hi : injective i.
Let e := attaching_homeomorphism h.

Definition pushout_right_injective :=
  @injective_homeomorphism_leg (attaching_space i j) Y X e
    (attaching_right i j) l (attaching_homeomorphism_right h)
    (@attaching_right_injective A B X i j hi).

Definition pushout_left_right (b : B) (x : X) :=
  iff_trans (@homeomorphism_leg_equality (attaching_space i j) Y B X e
    (attaching_left i j) (attaching_right i j) k l
    (attaching_homeomorphism_left h) (attaching_homeomorphism_right h) b x)
    (@attaching_left_right A B X i j hi b x).

Definition pushout_left_outside_fibre b (hb : ~ exists a, i a = b) b' :=
  iff_trans (@homeomorphism_leg_equality (attaching_space i j) Y B B e
    (attaching_left i j) (attaching_left i j) k k
    (attaching_homeomorphism_left h) (attaching_homeomorphism_left h) b' b)
    (@attaching_left_outside_fibre A B X i j hi b hb b').

Definition pushout_right_preimage_image :=
  @closed_pushout_right_preimage_image X Y l pushout_right_injective.
Definition pushout_left_preimage_right_image :=
  @closed_pushout_left_preimage_right_image A B X Y i j k l pushout_left_right.

Definition pushout_right_closed_image :=
  @closed_pushout_right_closed_image A B X Y i j k l pushout_right_injective
    pushout_left_right (pushout_closed_iff h).

Definition pushout_right_open_image :=
  @open_pushout_right_image A B X Y i j k l pushout_right_injective
    pushout_left_right (pushout_open_iff h).

Definition pushout_points_closed :=
  @closed_pushout_points_closed A B X Y i j k l pushout_right_injective
    pushout_left_right pushout_left_outside_fibre (pushout_closed_iff h) (pushout_cases h).

Definition pushout_accessible :=
  @closed_pushout_accessible A B X Y i j k l pushout_right_injective
    pushout_left_right pushout_left_outside_fibre (pushout_closed_iff h) (pushout_cases h).
End Actual.
End DPTopologicalPushoutEmbedding.
