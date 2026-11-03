(** The actual extra cone operator on the standard simplicial simplex. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators SimplexCategoryIdentities.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPStandardSimplexCone.
Import DPSimplexCategory DPSimplexOperators DPSimplexIdentities.

Definition cone_function n d (f : ordinal_map n d) (i : 'I_n.+2) : 'I_d.+1.
Proof.
  destruct i as [[|i] hi].
  - exact ord0.
  - exact (f (@Ordinal n.+1 i hi)).
Defined.

Lemma cone_monotone n d (f : ordinal_map n d) (i j : 'I_n.+2) :
  (i <= j)%N -> (cone_function f i <= cone_function f j)%N.
Proof.
  destruct i as [[|i] hi], j as [[|j] hj]; intro hij; try discriminate hij.
  - exact (leqnn 0).
  - exact (leq0n _).
  - exact (@ordinal_monotone n d f (@Ordinal n.+1 i hi) (@Ordinal n.+1 j hj) hij).
Qed.

Definition cone n d (f : ordinal_map n d) : ordinal_map n.+1 d :=
  @OrdinalMap n.+1 d (@cone_function n d f) (@cone_monotone n d f).

Arguments cone {_ _} _.

Lemma cone_zero n d (f : ordinal_map n d) : cone f ord0 = ord0.
Proof. reflexivity. Qed.

Lemma cone_successor n d (f : ordinal_map n d) (i : 'I_n.+1) :
  cone f (vertex_successor i) = f i.
Proof.
  destruct i as [i hi].
  have e : vertex_successor (@Ordinal n.+1 i hi) = @Ordinal n.+2 i.+1 hi.
  { apply val_inj. reflexivity. }
  rewrite e. reflexivity.
Qed.

Lemma cone_face_zero n d (f : ordinal_map n d) :
  ordinal_map_compose (@coface n ord0) (cone f) = f.
Proof.
  apply ordinal_map_ext. intros [i hi].
  have e : @coface n ord0 (@Ordinal n.+1 i hi) = @Ordinal n.+2 i.+1 hi.
  { apply val_inj. reflexivity. }
  change (cone f (@coface n ord0 (@Ordinal n.+1 i hi)) = f (@Ordinal n.+1 i hi)).
  rewrite e. reflexivity.
Qed.

Lemma coface_vertex_successor n (i : 'I_n.+2) (j : 'I_n.+1) :
  coface (vertex_successor i) (vertex_successor j) = vertex_successor (coface i j).
Proof.
  destruct i as [i hi], j as [j hj]. apply val_inj.
  change (coface_value i.+1 j.+1 = (coface_value i j).+1).
  unfold coface_value. cbn. destruct (Nat.leb i j); reflexivity.
Qed.

Lemma cone_face_successor n d (f : ordinal_map n.+1 d) (i : 'I_n.+2) :
  ordinal_map_compose (coface (vertex_successor i)) (cone f) =
    cone (ordinal_map_compose (coface i) f).
Proof.
  apply ordinal_map_ext. intros [[|j] hj].
  - destruct i as [i hi]. reflexivity.
  - have ej : @Ordinal n.+2 j.+1 hj = vertex_successor (@Ordinal n.+1 j hj).
    { apply val_inj. reflexivity. }
    rewrite ej.
    change (cone f (coface (vertex_successor i) (vertex_successor (@Ordinal n.+1 j hj))) =
      cone (ordinal_map_compose (coface i) f) (vertex_successor (@Ordinal n.+1 j hj))).
    rewrite coface_vertex_successor !cone_successor. reflexivity.
Qed.

Definition zero_vertex d : ordinal_map 0 d :=
  @OrdinalMap 0 d (fun _ => ord0) (fun _ _ _ => leqnn 0).

Lemma cone_face_last_zero d (f : ordinal_map 0 d) :
  ordinal_map_compose (@coface 0 (vertex_successor (@ord0 0))) (cone f) = zero_vertex d.
Proof. apply ordinal_map_ext. intro i. have -> : i = ord0 := ord1 i. reflexivity. Qed.

End DPStandardSimplexCone.
