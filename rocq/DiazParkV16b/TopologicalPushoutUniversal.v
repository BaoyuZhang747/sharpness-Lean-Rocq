(** Continuous descent for the actual quotient and its pushout universal property. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology
  sigT_topology quotient_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory CategoryPushout TopologicalPushoutCarrier.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope quotient_scope.
Local Open Scope classical_set_scope.

Module DPTopologicalPushoutUniversal.
Import DPTopological DPCategoryPushout DPTopologicalPushoutCarrier.
Section Universal.
Variables A B X : topologicalType.
Variables (i : hom topological_category A B) (j : hom topological_category A X).
Variable Y : topologicalType.
Variables (f : hom topological_category B Y) (g : hom topological_category X Y).
Variable w : compose i f = compose j g.

Definition attaching_evaluate (p : attaching_raw B X) : Y :=
  match p with
  | @existT _ _ true b => f b
  | @existT _ _ false x => g x
  end.

Lemma attaching_evaluate_equivalent p q : attaching_equivalent i j p q ->
  attaching_evaluate p = attaching_evaluate q.
Proof.
move=> h; elim: h => [p0|p0 q0 h ih|p0 q0 r0 h ih k ih'|a].
- reflexivity.
- exact: esym ih.
- exact: etrans ih ih'.
- exact (congr1 (fun m : hom topological_category A Y => m a) w).
Qed.

Lemma attaching_evaluate_continuous : continuous attaching_evaluate.
Proof. move=> [[] x] U hU; exact: cts_fun. Qed.

Definition attaching_desc (z : attaching_space i j) : Y := attaching_evaluate (repr z).

Lemma attaching_desc_class p : attaching_desc (attaching_class i j p) = attaching_evaluate p.
Proof.
rewrite /attaching_desc; apply: attaching_evaluate_equivalent.
apply/attaching_class_eq; exact: reprK.
Qed.

Lemma attaching_desc_continuous : continuous attaching_desc.
Proof.
apply/quotient_continuous.
have e : (attaching_desc \o attaching_class i j) = attaching_evaluate.
  apply funext => p; exact: attaching_desc_class.
rewrite e; exact: attaching_evaluate_continuous.
Qed.

Definition attaching_desc_map : hom topological_category (attaching_space i j) Y :=
  continuous_map attaching_desc_continuous.

Lemma attaching_desc_left : compose (attaching_left_map i j) attaching_desc_map = f.
Proof. apply topological_hom_ext => b; exact: attaching_desc_class. Qed.
Lemma attaching_desc_right : compose (attaching_right_map i j) attaching_desc_map = g.
Proof. apply topological_hom_ext => x; exact: attaching_desc_class. Qed.

Lemma attaching_desc_unique (h : hom topological_category (attaching_space i j) Y) :
  compose (attaching_left_map i j) h = f -> compose (attaching_right_map i j) h = g ->
  h = attaching_desc_map.
Proof.
move=> hB hX; apply topological_hom_ext => z.
case: (attaching_cases z) => [[b <-]|[x <-]].
- change (h (attaching_left_map i j b) = attaching_desc_map (attaching_left_map i j b)).
  rewrite -(topological_compose_at (attaching_left_map i j) h b) hB.
  symmetry; exact: attaching_desc_class.
- change (h (attaching_right_map i j x) = attaching_desc_map (attaching_right_map i j x)).
  rewrite -(topological_compose_at (attaching_right_map i j) h x) hX.
  symmetry; exact: attaching_desc_class.
Qed.
End Universal.

Definition attaching_pushout {A B X : topologicalType}
  (i : hom topological_category A B) (j : hom topological_category A X) :
  pushout_square i j (attaching_left_map i j) (attaching_right_map i j).
Proof.
refine (@Build_pushout_square topological_category A B X (attaching_space i j)
  i j (attaching_left_map i j) (attaching_right_map i j) (attaching_commutes i j)
  (fun Y f g w => @attaching_desc_map A B X i j Y f g w) _ _ _).
- move=> Y f g w; exact: attaching_desc_left.
- move=> Y f g w; exact: attaching_desc_right.
- move=> Y f g w h; exact: attaching_desc_unique.
Defined.
End DPTopologicalPushoutUniversal.
