From mathcomp Require Import all_ssreflect order boolp.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryFactorization
  SimplexCategoryFactorizationSections.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPRealizationBoundaryFaces.
Import DPSimplexCategory DPSimplexFactorization DPSimplexSections.

Section Face.
Variable n : nat.
Variable A : {set 'I_n.+1}.
Variable hA : (0 < #|A|)%N.

Definition face_dimension := #|A|.-1.
Lemma face_cardinality : face_dimension.+1 = #|A|.
Proof. exact (prednK hA). Qed.

Lemma face_inhabited : exists x : 'I_n.+1, x \in A.
Proof. exact (elimT card_gt0P hA). Qed.

Definition face_base : 'I_n.+1 := proj1_sig (cid face_inhabited).
Lemma face_base_mem : face_base \in A.
Proof. exact (proj2_sig (cid face_inhabited)). Qed.

Definition face_enum : 'I_#|A| -> 'I_n.+1 := @Order.enum_val _ _ A.
Definition face_rank : 'I_n.+1 -> 'I_#|A| :=
  @Order.enum_rank_in _ _ face_base A face_base_mem.

Definition face_inclusion_function (i : 'I_face_dimension.+1) : 'I_n.+1 :=
  face_enum (cast_ord face_cardinality i).

Lemma face_inclusion_monotone (i j : 'I_face_dimension.+1) :
  (i <= j)%N -> (face_inclusion_function i <= face_inclusion_function j)%N.
Proof.
  intro hij.
  have h := @Order.le_enum_val _ [the finPOrderType _ of 'I_n.+1]
    (fun x y => leq_total x y) A
    (cast_ord face_cardinality i) (cast_ord face_cardinality j).
  change ((face_inclusion_function i <= face_inclusion_function j)%N =
    (i <= j)%N) in h. rewrite h. exact hij.
Qed.

Definition face_inclusion : ordinal_map face_dimension n :=
  @OrdinalMap face_dimension n face_inclusion_function face_inclusion_monotone.

Lemma face_inclusion_injective : ordinal_injective face_inclusion.
Proof.
  intros i j e. have h := @Order.enum_val_inj _ [the finPreorderType _ of 'I_n.+1]
    A (cast_ord face_cardinality i) (cast_ord face_cardinality j) e.
  apply val_inj. exact (f_equal (fun x : 'I_#|A| => nat_of_ord x) h).
Qed.

Lemma face_inclusion_mem i : face_inclusion i \in A.
Proof. exact (@Order.enum_valP _ [the finPreorderType _ of 'I_n.+1]
  A (cast_ord face_cardinality i)). Qed.

Definition face_rank_cast (x : 'I_n.+1) : 'I_face_dimension.+1 :=
  cast_ord (esym face_cardinality) (face_rank x).

Lemma face_rank_cast_inverse x (hx : x \in A) : face_inclusion (face_rank_cast x) = x.
Proof.
  change (face_enum (cast_ord face_cardinality
    (cast_ord (esym face_cardinality) (face_rank x))) = x).
  rewrite cast_ordKV. exact (@Order.enum_rankK_in _ [the finPreorderType _ of 'I_n.+1]
    face_base A face_base_mem x hx).
Qed.

Lemma face_inclusion_image x : (exists i, face_inclusion i = x) <-> x \in A.
Proof.
  split.
  - intros [i hi]. rewrite <- hi. exact (face_inclusion_mem i).
  - intro hx. exists (face_rank_cast x). exact (face_rank_cast_inverse hx).
Qed.

Lemma face_inclusion_nonsurjective (hproper : A != setT) : ~ ordinal_surjective face_inclusion.
Proof.
  intro h. have e : A = setT.
  { apply/setP. intro x. rewrite in_setT.
    apply/idP. exact (proj1 (face_inclusion_image x) (h x)). }
  by move: hproper; rewrite e eqxx.
Qed.

Section Factor.
Variable k : nat.
Variable f : ordinal_map k n.
Variable hf : forall i, f i \in A.

Lemma face_factor_monotone (i j : 'I_k.+1) :
  (i <= j)%N -> (face_rank_cast (f i) <= face_rank_cast (f j))%N.
Proof.
  intro hij.
  have h := @Order.le_enum_rank_in _ [the finPOrderType _ of 'I_n.+1]
    (fun x y => leq_total x y) face_base A face_base_mem
    (f i) (f j) (hf i) (hf j).
  change ((face_rank_cast (f i) <= face_rank_cast (f j))%N = (f i <= f j)%N) in h.
  rewrite h. exact (ordinal_monotone f hij).
Qed.

Definition face_factor : ordinal_map k face_dimension :=
  @OrdinalMap k face_dimension (fun i => face_rank_cast (f i)) face_factor_monotone.

Lemma face_factor_apply i : face_inclusion (face_factor i) = f i.
Proof. exact (face_rank_cast_inverse (hf i)). Qed.

Lemma face_factorization : ordinal_map_compose face_factor face_inclusion = f.
Proof. apply ordinal_map_ext. exact face_factor_apply. Qed.

End Factor.
End Face.

End DPRealizationBoundaryFaces.
