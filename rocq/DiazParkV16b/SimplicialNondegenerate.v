From mathcomp Require Import all_ssreflect order boolp.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryFactorization
  SimplexCategoryFactorizationSections SimplexCategoryFactorizationProperties SimplicialSet.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialNondegenerate.
Import DPSimplexCategory DPSimplexFactorization DPSimplexSections
  DPSimplexFactorizationProperties DPSimplicialSet.

(** Degeneracy means pullback along a genuine proper ordinal surjection. *)
Definition degenerate (X : simplicial_set) n (x : simplex X n) : Prop :=
  exists m, (m < n)%N /\ exists q : ordinal_map n m,
    ordinal_surjective q /\ exists y : simplex X m, simplex_map X q y = x.

Arguments degenerate _ {_} _.

Definition nondegenerate (X : simplicial_set) n (x : simplex X n) : Prop :=
  ~ degenerate X x.

Arguments nondegenerate _ {_} _.

Lemma zero_simplex_nondegenerate (X : simplicial_set) (x : simplex X 0) :
  nondegenerate X x.
Proof. intros [m [h _]]. by rewrite ltn0 in h. Qed.

Theorem nondegenerate_core_exists (X : simplicial_set) n (x : simplex X n) :
  exists m, exists q : ordinal_map n m, exists y : simplex X m,
    ordinal_surjective q /\ nondegenerate X y /\ simplex_map X q y = x.
Proof.
  revert x. pattern n. apply ltn_ind. clear n.
  intros n ih x. destruct (pselect (degenerate X x)) as [hd|hnd].
  - destruct hd as [m [hm [q [hq [y hy]]]]].
    destruct (ih m hm y) as [k [r [z [hr [hz he]]]]].
    exists k, (ordinal_map_compose q r), z.
    split; first exact (ordinal_compose_surjective hq hr).
    split; first exact hz. rewrite simplex_map_compose he. exact hy.
  - exists n, (ordinal_map_identity n), x.
    split; first exact (@ordinal_identity_surjective n).
    split; first exact hnd. apply simplex_map_identity.
Qed.

Lemma nondegenerate_pullback_injective (X : simplicial_set) n m
    (f : ordinal_map n m) (y : simplex X m)
    (hy : nondegenerate X (simplex_map X f y)) : ordinal_injective f.
Proof.
  destruct (pselect (ordinal_injective f)) as [hf|hf]; first exact hf.
  exfalso. apply hy.
  exists (ordinal_image_dimension f). split.
  - exact (noninjective_image_dimension_lt hf).
  - exists (image_surjection f). split.
    + exact (@image_surjection_surjective n m f).
    + exists (simplex_map X (image_injection f) y).
      rewrite <- simplex_map_compose. rewrite (image_factorization f). reflexivity.
Qed.

Lemma nondegenerate_surjective_pullback_dimension (X : simplicial_set) n m
    (f : ordinal_map n m) (hf : ordinal_surjective f) (y : simplex X m)
    (hy : nondegenerate X (simplex_map X f y)) : n = m.
Proof.
  apply/eqP. rewrite eqn_leq. apply/andP. split.
  - exact (ordinal_injective_dimension (nondegenerate_pullback_injective hy)).
  - exact (ordinal_surjective_dimension hf).
Qed.

End DPSimplicialNondegenerate.
