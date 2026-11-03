From mathcomp Require Import all_ssreflect order boolp.
From DiazParkV16b Require Import SimplexCategory.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplexFactorization.
Import DPSimplexCategory.

Definition ordinal_surjective n m (f : ordinal_map n m) : Prop :=
  forall y, exists x, f x = y.

Definition ordinal_injective n m (f : ordinal_map n m) : Prop := injective f.

Section ImageFactorization.
Context (n m : nat) (f : ordinal_map n m).

Definition ordinal_image : {pred 'I_m.+1} := [pred y | y \in codom f].

Lemma ordinal_image_mem (x : 'I_n.+1) : f x \in ordinal_image.
Proof. apply/codomP. exists x. reflexivity. Qed.

Lemma ordinal_image_positive : (0 < #|ordinal_image|)%N.
Proof. apply/card_gt0P. exists (f ord0). apply ordinal_image_mem. Qed.

Definition ordinal_image_dimension := #|ordinal_image|.-1.

Lemma ordinal_image_cardinality : ordinal_image_dimension.+1 = #|ordinal_image|.
Proof. exact (prednK ordinal_image_positive). Qed.

Definition image_enum (i : 'I_#|ordinal_image|) : 'I_m.+1 :=
  @Order.enum_val _ [the finPreorderType _ of 'I_m.+1] ordinal_image i.

Definition image_rank (y : 'I_m.+1) : 'I_#|ordinal_image| :=
  @Order.enum_rank_in _ [the finPreorderType _ of 'I_m.+1]
    (f ord0) ordinal_image (ordinal_image_mem ord0) y.

Lemma ordinal_order_total (i j : 'I_m.+1) : (i <= j)%O || (j <= i)%O.
Proof. exact (leq_total i j). Qed.

Lemma image_enum_monotone (i j : 'I_#|ordinal_image|) :
  (i <= j)%N -> (image_enum i <= image_enum j)%N.
Proof.
  intro hij.
  have h := @Order.le_enum_val _ [the finPOrderType _ of 'I_m.+1]
    ordinal_order_total ordinal_image i j.
  change ((image_enum i <= image_enum j)%N = (i <= j)%N) in h.
  rewrite h. exact hij.
Qed.

Lemma image_rank_monotone (i j : 'I_n.+1) :
  (i <= j)%N -> (image_rank (f i) <= image_rank (f j))%N.
Proof.
  intro hij.
  have h := @Order.le_enum_rank_in _ [the finPOrderType _ of 'I_m.+1]
    ordinal_order_total (f ord0) ordinal_image (ordinal_image_mem ord0)
    (f i) (f j) (ordinal_image_mem i) (ordinal_image_mem j).
  change ((image_rank (f i) <= image_rank (f j))%N = (f i <= f j)%N) in h.
  rewrite h. exact (ordinal_monotone f hij).
Qed.

Definition image_injection_function (i : 'I_ordinal_image_dimension.+1) : 'I_m.+1 :=
  image_enum (cast_ord ordinal_image_cardinality i).

Definition image_surjection_function (i : 'I_n.+1) : 'I_ordinal_image_dimension.+1 :=
  cast_ord (esym ordinal_image_cardinality) (image_rank (f i)).

Definition image_injection : ordinal_map ordinal_image_dimension m.
Proof.
  refine (@OrdinalMap ordinal_image_dimension m image_injection_function _).
  intros i j hij. apply image_enum_monotone. exact hij.
Defined.

Definition image_surjection : ordinal_map n ordinal_image_dimension.
Proof.
  refine (@OrdinalMap n ordinal_image_dimension image_surjection_function _).
  intros i j hij. exact (image_rank_monotone hij).
Defined.

Lemma image_factorization_apply (i : 'I_n.+1) :
  image_injection (image_surjection i) = f i.
Proof.
  change (image_enum (cast_ord ordinal_image_cardinality
    (cast_ord (esym ordinal_image_cardinality) (image_rank (f i)))) = f i).
  rewrite cast_ordKV.
  exact (@Order.enum_rankK_in _ [the finPreorderType _ of 'I_m.+1]
    (f ord0) ordinal_image (ordinal_image_mem ord0) (f i) (ordinal_image_mem i)).
Qed.

Lemma image_factorization : ordinal_map_compose image_surjection image_injection = f.
Proof. apply ordinal_map_ext. exact image_factorization_apply. Qed.

Lemma image_injection_injective : ordinal_injective image_injection.
Proof.
  intros i j h.
  have hc := @Order.enum_val_inj _ [the finPreorderType _ of 'I_m.+1]
    ordinal_image (cast_ord ordinal_image_cardinality i)
    (cast_ord ordinal_image_cardinality j) h.
  apply val_inj.
  exact (f_equal (fun x : 'I_#|ordinal_image| => nat_of_ord x) hc).
Qed.

Lemma image_surjection_surjective : ordinal_surjective image_surjection.
Proof.
  intro j.
  have hm := @Order.enum_valP _ [the finPreorderType _ of 'I_m.+1]
    ordinal_image (cast_ord ordinal_image_cardinality j).
  have hc : image_injection j \in codom f := hm.
  move/codomP: hc => [i hi]. exists i.
  apply image_injection_injective. rewrite image_factorization_apply.
  symmetry. exact hi.
Qed.

End ImageFactorization.

End DPSimplexFactorization.
