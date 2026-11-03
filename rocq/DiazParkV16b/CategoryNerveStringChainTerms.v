(** The actual degreewise free-module equivalence from functor simplices of the
    nerve to category strings, including augmentation and functoriality. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category BarPaths BarFreeModule.
From DiazParkV16b Require Import SimplicialSet SimplicialChains SimplicialChainsMaps
  CategoryNerve CategoryNervePathsPrefix CategoryNervePaths CategoryNervePathsNaturality
  CategoryStringChains CategoryStringChainsMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPCategoryNerve DPCategoryNervePaths
  DPCategoryNervePathEquivalence DPCategoryNervePathNaturality DPSimplicialSet.
Local Open Scope ring_scope.

Section Terms.
Variable R : pzRingType.
Variable C : category.

Definition nerve_to_string_at n :
    {linear DPSimplicialChains.term R (nerve C) n -> category_string_term R C n} :=
  free_map R (@nerve_path C n).

Definition string_to_nerve_at n :
    {linear category_string_term R C n -> DPSimplicialChains.term R (nerve C) n} :=
  free_map R (@path_nerve C n).

Lemma nerve_to_string_inverse n (v : category_string_term R C n) :
    nerve_to_string_at n (string_to_nerve_at n v) = v.
Proof.
apply (free_lift_ext
  (g := (nerve_to_string_at n \o string_to_nerve_at n : {linear _ -> _}))
  (h := (idfun : {linear _ -> _}))).
intro s; rewrite /= /nerve_to_string_at /string_to_nerve_at !free_map_basis.
by rewrite nerve_path_nerve.
Qed.

Lemma string_to_nerve_inverse n (v : DPSimplicialChains.term R (nerve C) n) :
    string_to_nerve_at n (nerve_to_string_at n v) = v.
Proof.
apply (free_lift_ext
  (g := (string_to_nerve_at n \o nerve_to_string_at n : {linear _ -> _}))
  (h := (idfun : {linear _ -> _}))).
intro s; rewrite /= /nerve_to_string_at /string_to_nerve_at !free_map_basis.
by rewrite path_nerve_path.
Qed.

Lemma nerve_to_string_augmentation (v : DPSimplicialChains.term R (nerve C) 0%N) :
    category_string_augmentation R C (nerve_to_string_at 0%N v) =
    DPSimplicialChains.augmentation R (nerve C) v.
Proof.
apply (free_lift_ext
  (g := (category_string_augmentation R C \o nerve_to_string_at 0%N : {linear _ -> _}))
  (h := DPSimplicialChains.augmentation R (nerve C))).
intro s.
change (category_string_augmentation R C (nerve_to_string_at 0%N (free_basis R s)) =
  DPSimplicialChains.augmentation R (nerve C) (free_basis R s)).
rewrite /nerve_to_string_at free_map_basis
  category_string_augmentation_basis DPSimplicialChains.augmentation_basis.
reflexivity.
Qed.

Lemma string_to_nerve_augmentation (v : category_string_term R C 0%N) :
    DPSimplicialChains.augmentation R (nerve C) (string_to_nerve_at 0%N v) =
    category_string_augmentation R C v.
Proof. by rewrite -nerve_to_string_augmentation nerve_to_string_inverse. Qed.
End Terms.

Section Naturality.
Variable R : pzRingType.
Variables C D : category.
Variable F : functor C D.

Lemma nerve_to_string_naturality n (v : DPSimplicialChains.term R (nerve C) n) :
    nerve_to_string_at R D n (DPSimplicialChainMaps.map_at R (nerve_map F) n v) =
    category_string_map_at R F n (nerve_to_string_at R C n v).
Proof.
apply (free_lift_ext
  (g := (nerve_to_string_at R D n \o DPSimplicialChainMaps.map_at R (nerve_map F) n : {linear _ -> _}))
  (h := (category_string_map_at R F n \o nerve_to_string_at R C n : {linear _ -> _}))).
intro s; rewrite /= /nerve_to_string_at /DPSimplicialChainMaps.map_at
  /category_string_map_at !free_map_basis.
congr (free_basis R _).
exact: nerve_path_postcompose.
Qed.

Lemma string_to_nerve_naturality n (v : category_string_term R C n) :
    string_to_nerve_at R D n (category_string_map_at R F n v) =
    DPSimplicialChainMaps.map_at R (nerve_map F) n (string_to_nerve_at R C n v).
Proof.
apply (can_inj (@string_to_nerve_inverse R D n)).
by rewrite nerve_to_string_inverse nerve_to_string_naturality nerve_to_string_inverse.
Qed.
End Naturality.
