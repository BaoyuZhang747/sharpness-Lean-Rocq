(** Functorial maps of actual category-string chains. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category BarPaths BarFreeModule.
From DiazParkV16b Require Import ChainComplex CategoryBarPullbackPaths CategoryStringChains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkFreeModule DPChainComplex DPCategoryBarPullback.
Local Open Scope ring_scope.

Section Maps.
Variable R : pzRingType.
Variables C D : category.
Variable F : functor C D.

Definition category_string_map_at n : {linear category_string_term R C n -> category_string_term R D n} :=
  free_map R (path_map F n).

Lemma category_string_map_face n i (v : category_string_term R C n.+1) :
    @category_string_face R D n i (category_string_map_at n.+1 v) =
    category_string_map_at n (@category_string_face R C n i v).
Proof.
apply (free_lift_ext
  (g := (@category_string_face R D n i \o category_string_map_at n.+1 : {linear _ -> _}))
  (h := (category_string_map_at n \o @category_string_face R C n i : {linear _ -> _}))).
intro s; rewrite /= /category_string_map_at /category_string_face !free_map_basis.
by rewrite path_map_face.
Qed.

Lemma category_string_map_boundary n (v : category_string_term R C n.+1) :
    @category_string_boundary R D n (category_string_map_at n.+1 v) =
    category_string_map_at n (@category_string_boundary R C n v).
Proof.
rewrite /category_string_boundary linear_sum.
apply eq_bigr; intros i _; by rewrite linearZ category_string_map_face.
Qed.

Definition category_string_chain_map : chain_map (category_string_chain R C) (category_string_chain R D) :=
  @ChainMap R (category_string_chain R C) (category_string_chain R D)
    category_string_map_at category_string_map_boundary.

Lemma category_string_map_augmentation (v : category_string_term R C 0%N) :
    category_string_augmentation R D (category_string_map_at 0%N v) =
    category_string_augmentation R C v.
Proof.
apply (free_lift_ext
  (g := (category_string_augmentation R D \o category_string_map_at 0%N : {linear _ -> _}))
  (h := category_string_augmentation R C)).
intro s; rewrite /= /category_string_map_at free_map_basis !category_string_augmentation_basis.
reflexivity.
Qed.
End Maps.

Lemma category_string_map_identity (R : pzRingType) (C : category) n (v : category_string_term R C n) :
    category_string_map_at R (functor_id C) n v = v.
Proof.
have h : path_map (functor_id C) n = idfun.
  apply functional_extensionality_dep; exact: path_map_identity.
by rewrite /category_string_map_at h free_map_identity.
Qed.

Lemma category_string_map_composition (R : pzRingType) {C D E : category}
    (F : functor C D) (G : functor D E) n (v : category_string_term R C n) :
    category_string_map_at R (functor_comp F G) n v =
    category_string_map_at R G n (category_string_map_at R F n v).
Proof.
have h : path_map (functor_comp F G) n = path_map G n \o path_map F n.
  apply functional_extensionality_dep; exact: path_map_composition.
by rewrite /category_string_map_at h free_map_composition.
Qed.
