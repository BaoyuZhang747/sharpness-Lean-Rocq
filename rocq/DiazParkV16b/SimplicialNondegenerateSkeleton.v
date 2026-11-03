From mathcomp Require Import all_ssreflect order boolp.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryFactorization
  SimplexCategoryFactorizationSections SimplexCategoryFactorizationProperties
  SimplicialSet SimplicialSubcomplex SimplicialSubcomplexGenerated SimplicialSkeleton
  SimplicialNondegenerate SimplicialNondegenerateUniqueness.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialNondegenerateSkeleton.
Import DPSimplexCategory DPSimplexFactorization DPSimplexSections
  DPSimplexFactorizationProperties DPSimplicialSet DPSimplicialSubcomplex
  DPSimplicialGenerated DPSimplicialSkeleton DPSimplicialNondegenerate
  DPSimplicialNondegenerateUniqueness.

Lemma surjective_pullback_subcomplex_iff X (S : subcomplex X) n m
    (q : ordinal_map n m) (hq : ordinal_surjective q) (y : simplex X m) :
  member S n (simplex_map X q y) <-> member S m y.
Proof.
  split.
  - intro h. have h' := member_closed S (ordinal_section hq) _ h.
    rewrite <- simplex_map_compose in h'.
    rewrite ordinal_section_right_inverse simplex_map_identity in h'. exact h'.
  - exact (member_closed S q y).
Qed.

Theorem nondegenerate_core_skeleton_iff X r n m
    (q : ordinal_map n m) (hq : ordinal_surjective q) (y : simplex X m)
    (hy : nondegenerate X y) :
  member (skeleton X r) n (simplex_map X q y) <-> (m <= r)%N.
Proof.
  split.
  - intros [k [z [g [hk he]]]]. exact (leq_trans
      (@nondegenerate_core_least_dimension X n m k q hq g y z hy (esym he)) hk).
  - intro h. exists m, y, q. split; [exact h|reflexivity].
Qed.

Lemma nondegenerate_skeleton_iff X r n (x : simplex X n)
    (hx : nondegenerate X x) :
  member (skeleton X r) n x <-> (n <= r)%N.
Proof.
  have h := @nondegenerate_core_skeleton_iff X r n n (ordinal_map_identity n)
    (@ordinal_identity_surjective n) x hx.
  rewrite simplex_map_identity in h. exact h.
Qed.

Theorem skeleton_generated_by_nondegenerate X r :
  skeleton X r = generated_subcomplex
    (fun n x => (n <= r)%N /\ nondegenerate X x).
Proof.
  apply subcomplex_le_antisymm.
  - apply (proj2 (@generated_le X (fun n (_ : simplex X n) => (n <= r)%N) _)).
    intros n x hn.
    destruct (@nondegenerate_core_exists X n x) as [m [q [y [hq [hy he]]]]].
    exists m, y, q. split; last exact he. split; last exact hy.
    exact (leq_trans (ordinal_surjective_dimension hq) hn).
  - apply (proj2 (@generated_le X
      (fun n x => (n <= r)%N /\ nondegenerate X x) (skeleton X r))).
    intros n x [hn _]. exact (skeleton_contains_degree x hn).
Qed.

End DPSimplicialNondegenerateSkeleton.
