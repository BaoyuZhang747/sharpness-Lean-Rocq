(** Closed injections and T1 separation for actual attaching pushouts. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalPushoutCarrier TopologicalPushoutFibres.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module DPTopologicalPushoutSeparation.
Import DPTopological DPTopologicalPushoutCarrier DPTopologicalPushoutFibres.
Section Separation.
Variables A B X Y : topologicalType.
Variables (i : hom topological_category A B) (j : hom topological_category A X).
Variables (k : hom topological_category B Y) (l : hom topological_category X Y).
Hypothesis hlinj : injective l.
Hypothesis hcross : forall b x, k b = l x <-> exists a, i a = b /\ j a = x.
Hypothesis houtside : forall b, (~ exists a, i a = b) -> forall b', k b' = k b <-> b' = b.
Hypothesis hfinal : forall S : set Y, closed S <-> closed (k @^-1` S) /\ closed (l @^-1` S).
Hypothesis hcover : forall y : Y, (exists b, k b = y) \/ (exists x, l x = y).
Hypothesis hi_closed : forall S : set A, closed S -> closed (i @` S).

Lemma closed_pushout_right_preimage_image (S : set X) :
  l @^-1` (l @` S) = S.
Proof.
apply/seteqP; split=> x.
- move=> [y hy e]. have -> : x = y := esym (@hlinj _ _ e).
  exact hy.
- move=> hx; by exists x.
Qed.

Lemma closed_pushout_left_preimage_right_image (S : set X) :
  k @^-1` (l @` S) = i @` (j @^-1` S).
Proof.
apply/seteqP; split=> b.
- move=> [x hx e]. have [a [ha haj]] := proj1 (hcross b x) (esym e).
  exists a; [change (S (j a)); by rewrite haj | exact ha].
- move=> [a ha <-]. exists (j a); first exact ha.
  symmetry; apply (proj2 (hcross (i a) (j a))).
  by exists a.
Qed.

Theorem closed_pushout_right_closed_image (S : set X) : closed S -> closed (l @` S).
Proof.
move=> hS; apply/hfinal; split.
- rewrite closed_pushout_left_preimage_right_image; apply: hi_closed.
  apply: preimage_closed; [by move=> x hx; exact: cts_fun | exact hS].
- by rewrite closed_pushout_right_preimage_image.
Qed.

Lemma closed_pushout_left_outside_closed (b : B) (hb : ~ exists a, i a = b)
  (hB : forall b : B, closed [set b]) : closed [set k b].
Proof.
apply/hfinal; split.
- have he : k @^-1` [set k b] = [set b].
    apply/seteqP; split=> b'.
    * change (k b' = k b -> b' = b).
      exact (proj1 (@houtside b hb b')).
    * change (b' = b -> k b' = k b). by move=> ->.
  rewrite he; exact: hB.
- have he : l @^-1` [set k b] = set0.
    apply/seteqP; split=> x; last by [].
    move=> e; have [a [ha _]] := proj1 (hcross b x) (esym e).
    exfalso; apply hb; by exists a.
  rewrite he; exact: closed0.
Qed.

Theorem closed_pushout_points_closed
  (hB : forall b : B, closed [set b]) (hX : forall x : X, closed [set x])
  (z : Y) : closed [set z].
Proof.
case: (hcover z) => [[b <-]|[x <-]].
- case: (pselect (exists a, i a = b)) => [[a <-]|hb].
  + have e : k (i a) = l (j a).
      apply (proj2 (hcross (i a) (j a))). by exists a.
    rewrite e -image_set1; exact: closed_pushout_right_closed_image (hX _).
  + exact: closed_pushout_left_outside_closed hb hB.
- rewrite -image_set1; exact: closed_pushout_right_closed_image (hX _).
Qed.

Theorem closed_pushout_accessible (hB : accessible_space B) (hX : accessible_space X) :
  accessible_space (Y).
Proof.
move=> x y hxy; exists (~` [set y]); constructor.
- rewrite openC; apply: closed_pushout_points_closed;
    [exact: accessible_closed_set1 hB | exact: accessible_closed_set1 hX].
- by rewrite inE /=; exact/eqP.
- by rewrite inE /=.
Qed.
End Separation.
End DPTopologicalPushoutSeparation.
