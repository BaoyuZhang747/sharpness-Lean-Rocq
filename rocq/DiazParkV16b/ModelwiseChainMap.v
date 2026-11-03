(** Natural chain-map extension from genuine model generators and actual exactness. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules.
From DiazParkV16b Require Import ModelwiseChainDiagram ModelwisePresentation.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPModelwiseChainDiagram DPModelwisePresentation.
Local Open Scope ring_scope.

Module DPModelwiseChainMap.
Section Extension.
Variable R : pzRingType.
Variable C : category.
Variables P Q : chain_diagram R C.
Variable I : nat -> Type.
Variable models : forall n, I n -> C.
Arguments models _ _ : clear implicits.
Variable pres : forall n, model_presentation (models n) (diagram_degree P n).
Variable a0 : nat_trans (diagram_degree P 0%N) (diagram_degree Q 0%N).
Variable h1 : forall i : I 1%N, exists y : fobj (diagram_degree Q 1%N) (models 1%N i),
  diagram_apply (diagram_d Q 0%N) (models 1%N i) y =
  diagram_apply a0 (models 1%N i)
    (diagram_apply (diagram_d P 0%N) (models 1%N i) (model_generator (pres 1%N) i)).
Variable hpos : forall n (i : I n.+2) (x : fobj (diagram_degree Q n.+1) (models n.+2 i)),
  diagram_apply (diagram_d Q n) (models n.+2 i) x = 0 ->
  exists y, diagram_apply (diagram_d Q n.+1) (models n.+2 i) y = x.

Definition first_target := nat_comp (diagram_d P 0%N) a0.
Definition first_map : nat_trans (diagram_degree P 1%N) (diagram_degree Q 1%N) :=
  @lift_along R C (I 1%N) (models 1%N) (diagram_degree P 1%N) (pres 1%N)
    (diagram_degree Q 1%N) (diagram_degree Q 0%N) (diagram_d Q 0%N) first_target h1.

Lemma first_map_d (X : C) (x : fobj (diagram_degree P 1%N) X) :
  diagram_apply (diagram_d Q 0%N) X (diagram_apply first_map X x) =
  diagram_apply a0 X (diagram_apply (diagram_d P 0%N) X x).
Proof. exact: lift_along_apply. Qed.

Record extension_step n := ExtensionStep {
  extension_map : nat_trans (diagram_degree P n.+1) (diagram_degree Q n.+1);
  extension_next_cycle : forall X (x : fobj (diagram_degree P n.+2) X),
    diagram_apply (diagram_d Q n) X
      (diagram_apply extension_map X (diagram_apply (diagram_d P n.+1) X x)) = 0
}.
Arguments extension_next_cycle {n} e X x.

Definition first_step : extension_step 0%N.
Proof.
refine (@ExtensionStep 0%N first_map _).
move=> X x; rewrite first_map_d diagram_d_squared.
exact: module_hom_zero.
Defined.

Definition next_target n (s : extension_step n) := nat_comp (diagram_d P n.+1) (extension_map s).
Lemma next_preimage n (s : extension_step n) (i : I n.+2) :
  exists y, diagram_apply (diagram_d Q n.+1) (models n.+2 i) y =
    diagram_apply (next_target s) (models n.+2 i) (model_generator (pres n.+2) i).
Proof.
apply (@hpos n i).
exact: extension_next_cycle.
Qed.

Definition next_map n (s : extension_step n) : nat_trans (diagram_degree P n.+2) (diagram_degree Q n.+2) :=
  @lift_along R C (I n.+2) (models n.+2) (diagram_degree P n.+2) (pres n.+2)
    (diagram_degree Q n.+2) (diagram_degree Q n.+1) (diagram_d Q n.+1) (next_target s) (@next_preimage n s).

Lemma next_map_d n (s : extension_step n) (X : C) (x : fobj (diagram_degree P n.+2) X) :
  diagram_apply (diagram_d Q n.+1) X (diagram_apply (next_map s) X x) =
  diagram_apply (extension_map s) X (diagram_apply (diagram_d P n.+1) X x).
Proof. exact: lift_along_apply. Qed.

Definition next_step n (s : extension_step n) : extension_step n.+1.
Proof.
refine (@ExtensionStep n.+1 (next_map s) _).
move=> X x; rewrite next_map_d diagram_d_squared.
exact: module_hom_zero.
Defined.

Fixpoint constructed_step n : extension_step n :=
  match n as k return extension_step k with
  | 0%N => first_step
  | k.+1 => next_step (constructed_step k)
  end.

Definition extension_degree n : nat_trans (diagram_degree P n) (diagram_degree Q n) :=
  match n as k return nat_trans (diagram_degree P k) (diagram_degree Q k) with
  | 0%N => a0
  | k.+1 => extension_map (constructed_step k)
  end.

Lemma extension_degree_d n (X : C) (x : fobj (diagram_degree P n.+1) X) :
  diagram_apply (diagram_d Q n) X (diagram_apply (extension_degree n.+1) X x) =
  diagram_apply (extension_degree n) X (diagram_apply (diagram_d P n) X x).
Proof.
case: n x => [|n] x; [exact: first_map_d | exact: next_map_d].
Qed.

Definition modelwise_chain_map : chain_diagram_map P Q :=
  @ChainDiagramMap R C P Q extension_degree extension_degree_d.

Lemma modelwise_chain_map_zero : diagram_map_degree modelwise_chain_map 0%N = a0.
Proof. reflexivity. Qed.
End Extension.
End DPModelwiseChainMap.
