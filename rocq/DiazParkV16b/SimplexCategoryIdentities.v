From Stdlib Require Import Arith.PeanoNat Lia.
From mathcomp Require Import all_ssreflect boolp.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplexIdentities.
Import DPSimplexCategory DPSimplexOperators.

Ltac ordinal_arithmetic :=
  unfold coface_value, codegeneracy_value;
  repeat match goal with
  | |- context [Nat.leb ?x ?y] => destruct (Nat.leb_spec0 x y)
  | |- context [Nat.ltb ?x ?y] => destruct (Nat.ltb_spec0 x y)
  end; cbn in *; lia.

Lemma coface_value_coface i j x : (i <= j)%coq_nat ->
  coface_value i (coface_value j x) =
    coface_value (S j) (coface_value i x).
Proof. intro h. ordinal_arithmetic. Qed.

Lemma codegeneracy_value_codegeneracy i j x : (i <= j)%coq_nat ->
  codegeneracy_value i (codegeneracy_value (S j) x) =
    codegeneracy_value j (codegeneracy_value i x).
Proof. intro h. ordinal_arithmetic. Qed.

Lemma codegeneracy_value_coface_lt i j x : (i < j)%coq_nat ->
  codegeneracy_value j (coface_value i x) =
    coface_value i (codegeneracy_value (Nat.pred j) x).
Proof. intro h. ordinal_arithmetic. Qed.

Lemma codegeneracy_value_coface_same i x :
  codegeneracy_value i (coface_value i x) = x.
Proof. ordinal_arithmetic. Qed.

Lemma codegeneracy_value_coface_successor i x :
  codegeneracy_value i (coface_value (S i) x) = x.
Proof. ordinal_arithmetic. Qed.

Lemma codegeneracy_value_coface_gt i j x : (S j < i)%coq_nat ->
  codegeneracy_value j (coface_value i x) =
    coface_value (Nat.pred i) (codegeneracy_value j x).
Proof. intro h. ordinal_arithmetic. Qed.

Definition vertex_widen n (i : 'I_n.+1) : 'I_n.+2 :=
  @Ordinal n.+2 i (ltn_trans (ltn_ord i) (ltnSn n.+1)).

Definition vertex_successor n (i : 'I_n.+1) : 'I_n.+2.
Proof. refine (@Ordinal n.+2 (val i).+1 _). by rewrite ltnS; apply ltn_ord. Defined.

Arguments vertex_widen {_} _.
Arguments vertex_successor {_} _.

Lemma coface_coface n (i j : 'I_n.+2) : (i <= j)%N ->
  ordinal_map_compose (coface j) (coface (vertex_widen i)) =
    ordinal_map_compose (coface i) (coface (vertex_successor j)).
Proof.
  intro hij. apply ordinal_map_ext. intro x. apply val_inj.
  change (coface_value i (coface_value j x) =
    coface_value (S j) (coface_value i x)).
  apply coface_value_coface. exact (elimT leP hij).
Qed.

Lemma codegeneracy_codegeneracy n (i j : 'I_n.+1) : (i <= j)%N ->
  ordinal_map_compose (codegeneracy (vertex_successor j)) (codegeneracy i) =
    ordinal_map_compose (codegeneracy (vertex_widen i)) (codegeneracy j).
Proof.
  intro hij. apply ordinal_map_ext. intro x. apply val_inj.
  change (codegeneracy_value i (codegeneracy_value (S j) x) =
    codegeneracy_value j (codegeneracy_value i x)).
  apply codegeneracy_value_codegeneracy. exact (elimT leP hij).
Qed.

Lemma coface_codegeneracy_same n (i : 'I_n.+1) :
  ordinal_map_compose (coface (vertex_widen i)) (codegeneracy i) =
    ordinal_map_identity n.
Proof.
  apply ordinal_map_ext. intro x. apply val_inj.
  exact (codegeneracy_value_coface_same i x).
Qed.

Lemma coface_codegeneracy_successor n (i : 'I_n.+1) :
  ordinal_map_compose (coface (vertex_successor i)) (codegeneracy i) =
    ordinal_map_identity n.
Proof.
  apply ordinal_map_ext. intro x. apply val_inj.
  exact (codegeneracy_value_coface_successor i x).
Qed.

Lemma coface_codegeneracy_lt n (i : 'I_n.+2) (j : 'I_n.+1) : (i <= j)%N ->
  ordinal_map_compose (coface (vertex_widen i))
    (codegeneracy (vertex_successor j)) =
  ordinal_map_compose (codegeneracy j) (coface i).
Proof.
  intro hij. apply ordinal_map_ext. intro x. apply val_inj.
  change (codegeneracy_value (S j) (coface_value i x) =
    coface_value i (codegeneracy_value j x)).
  apply codegeneracy_value_coface_lt.
  have h : (val i <= val j)%coq_nat := elimT leP hij. cbn in *; lia.
Qed.

Lemma coface_codegeneracy_gt n (i : 'I_n.+1) (j : 'I_n.+2) : (i < j)%N ->
  ordinal_map_compose (coface (vertex_successor j))
    (codegeneracy (vertex_widen i)) =
  ordinal_map_compose (codegeneracy i) (coface j).
Proof.
  intro hij. apply ordinal_map_ext. intro x. apply val_inj.
  change (codegeneracy_value i (coface_value (S j) x) =
    coface_value j (codegeneracy_value i x)).
  apply codegeneracy_value_coface_gt.
  have h : (val i < val j)%coq_nat := elimT ltP hij. cbn in *; lia.
Qed.

End DPSimplexIdentities.
