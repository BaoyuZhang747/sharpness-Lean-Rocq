(** Transfer the explicit attaching quotient to any genuine topological pushout. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory CategoryPushout
  CategoryPushoutComparison TopologicalPushoutCarrier TopologicalPushoutUniversal.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module DPTopologicalPushoutComparison.
Import DPTopological DPCategoryPushout DPCategoryPushoutComparison
  DPTopologicalPushoutCarrier DPTopologicalPushoutUniversal.

Lemma homeomorphism_closed_iff {X Y : topologicalType} (e : homeomorphism X Y) (S : set Y) :
  closed S <-> closed (iso_hom e @^-1` S).
Proof.
split.
- move=> hS; apply: preimage_closed; [by move=> x hx; exact: cts_fun | exact hS].
- move=> hS.
  have he : S = iso_inv e @^-1` (iso_hom e @^-1` S).
    apply/seteqP; split=> y.
    * change (S y -> S (iso_hom e (iso_inv e y))). by rewrite homeomorphism_inverseK.
    * change (S (iso_hom e (iso_inv e y)) -> S y). by rewrite homeomorphism_inverseK.
  rewrite he; apply: preimage_closed; [by move=> x hx; exact: cts_fun | exact hS].
Qed.

Lemma homeomorphism_two_leg_cases {P Y B X : topologicalType} (e : homeomorphism P Y)
  (f : B -> P) (g : X -> P) (k : B -> Y) (l : X -> Y)
  (hf : forall b, iso_hom e (f b) = k b) (hg : forall x, iso_hom e (g x) = l x)
  (hc : forall p, (exists b, f b = p) \/ (exists x, g x = p)) (y : Y) :
  (exists b, k b = y) \/ (exists x, l x = y).
Proof.
case: (hc (iso_inv e y)) => [[b hb]|[x hx]].
- left; exists b; rewrite -hf hb; exact: homeomorphism_inverseK.
- right; exists x; rewrite -hg hx; exact: homeomorphism_inverseK.
Qed.

Lemma homeomorphism_two_leg_closed_iff {P Y B X : topologicalType} (e : homeomorphism P Y)
  (f : B -> P) (g : X -> P) (k : B -> Y) (l : X -> Y)
  (hf : forall b, iso_hom e (f b) = k b) (hg : forall x, iso_hom e (g x) = l x)
  (hfinal : forall T : set P, closed T <-> closed (f @^-1` T) /\ closed (g @^-1` T))
  (S : set Y) : closed S <-> closed (k @^-1` S) /\ closed (l @^-1` S).
Proof.
rewrite (homeomorphism_closed_iff e) hfinal.
have eB : f @^-1` (iso_hom e @^-1` S) = k @^-1` S.
  apply/seteqP; split=> b.
  * change (S (iso_hom e (f b)) -> S (k b)). by rewrite hf.
  * change (S (k b) -> S (iso_hom e (f b))). by rewrite hf.
have eX : g @^-1` (iso_hom e @^-1` S) = l @^-1` S.
  apply/seteqP; split=> x.
  * change (S (iso_hom e (g x)) -> S (l x)). by rewrite hg.
  * change (S (l x) -> S (iso_hom e (g x))). by rewrite hg.
by rewrite eB eX.
Qed.

Lemma two_leg_open_of_closed {Y B X : topologicalType} (k : B -> Y) (l : X -> Y)
  (hclosed : forall S, closed S <-> closed (k @^-1` S) /\ closed (l @^-1` S))
  (S : set Y) : open S <-> open (k @^-1` S) /\ open (l @^-1` S).
Proof. have h := hclosed (~` S). by rewrite !closedC in h. Qed.

Section Comparison.
Variables A B X Y : topologicalType.
Variables (i : hom topological_category A B) (j : hom topological_category A X)
  (k : hom topological_category B Y) (l : hom topological_category X Y).
Variable h : pushout_square i j k l.

Definition attaching_homeomorphism : homeomorphism (attaching_space i j) Y :=
  pushout_comparison_iso (attaching_pushout i j) h.

Lemma attaching_homeomorphism_left b : iso_hom attaching_homeomorphism (attaching_left i j b) = k b.
Proof.
exact (congr1 (fun f : hom topological_category B Y => f b)
  (pushout_comparison_left (attaching_pushout i j) h)).
Qed.
Lemma attaching_homeomorphism_right x : iso_hom attaching_homeomorphism (attaching_right i j x) = l x.
Proof.
exact (congr1 (fun f : hom topological_category X Y => f x)
  (pushout_comparison_right (attaching_pushout i j) h)).
Qed.

Definition pushout_cases :=
  @homeomorphism_two_leg_cases (attaching_space i j) Y B X attaching_homeomorphism
    (attaching_left i j) (attaching_right i j) k l
    attaching_homeomorphism_left attaching_homeomorphism_right (@attaching_cases A B X i j).

Definition pushout_closed_iff :=
  @homeomorphism_two_leg_closed_iff (attaching_space i j) Y B X attaching_homeomorphism
    (attaching_left i j) (attaching_right i j) k l
    attaching_homeomorphism_left attaching_homeomorphism_right (@attaching_closed_iff A B X i j).

Definition pushout_open_iff := @two_leg_open_of_closed Y B X k l pushout_closed_iff.

End Comparison.
End DPTopologicalPushoutComparison.
