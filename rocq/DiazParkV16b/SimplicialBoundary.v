From mathcomp Require Import all_ssreflect order boolp.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryFactorization
  SimplexCategoryFactorizationSections SimplexCategoryFactorizationProperties
  SimplicialSet SimplicialSubcomplex SimplicialSetYoneda.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialBoundary.
Import DPSimplexCategory DPSimplexFactorization DPSimplexSections
  DPSimplexFactorizationProperties DPSimplicialSet DPSimplicialSubcomplex
  DPSimplicialYoneda.

Lemma compose_surjective_right n m k (f : ordinal_map n m) (g : ordinal_map m k) :
  ordinal_surjective (ordinal_map_compose f g) -> ordinal_surjective g.
Proof. intros h z. destruct (h z) as [x hx]. exists (f x). exact hx. Qed.

Lemma ordinal_injective_same_dimension_surjective n m (f : ordinal_map n m)
    (hf : ordinal_injective f) (e : n = m) : ordinal_surjective f.
Proof.
  subst m. rewrite (ordinal_injective_self_identity hf).
  exact (@ordinal_identity_surjective n).
Qed.

Lemma nonsurjective_image_dimension_lt n m (f : ordinal_map n m)
    (hf : ~ ordinal_surjective f) : (ordinal_image_dimension f < m)%N.
Proof.
  rewrite ltn_neqAle. apply/andP. split.
  - apply/eqP. intro e. apply hf.
    rewrite <- (image_factorization f). apply ordinal_compose_surjective.
    + exact (@image_surjection_surjective n m f).
    + exact (@ordinal_injective_same_dimension_surjective _ _ _
        (@image_injection_injective n m f) e).
  - exact (ordinal_image_dimension_le_target f).
Qed.

(** The boundary consists of the ordinal maps whose image misses a vertex. *)
Definition boundary (n : nat) : subcomplex (standard_simplex n).
Proof.
  refine (@Subcomplex (standard_simplex n)
    (fun k f => ~ @ordinal_surjective k n f) _).
  intros k m f g hg h. apply hg. exact (compose_surjective_right h).
Defined.

Definition boundary_set n : simplicial_set := subcomplex_set (boundary n).
Definition boundary_inclusion n : simplicial_map (boundary_set n) (standard_simplex n) :=
  subcomplex_inclusion (boundary n).

Lemma boundary_member n k (f : ordinal_map k n) :
  member (boundary n) k f <-> ~ ordinal_surjective f.
Proof. reflexivity. Qed.

Lemma boundary_zero_empty k (x : simplex (boundary_set 0) k) : False.
Proof.
  destruct x as [f hf]. apply hf. intro y. exists ord0.
  rewrite (ord1 y) (ord1 (f ord0)). reflexivity.
Qed.

Definition boundary_characteristic X n (x : simplex X n) :
    simplicial_map (boundary_set n) X :=
  nat_comp (boundary_inclusion n) (characteristic_simplex X x).

End DPSimplicialBoundary.
