From mathcomp Require Import all_ssreflect order boolp.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryFactorization
  SimplexCategoryFactorizationSections SimplexCategoryFactorizationProperties
  SimplicialSet SimplicialNondegenerate.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialNondegenerateUniqueness.
Import DPSimplexCategory DPSimplexFactorization DPSimplexSections
  DPSimplexFactorizationProperties DPSimplicialSet DPSimplicialNondegenerate.

Lemma core_section_pullback (X : simplicial_set) n m k
    (f : ordinal_map n m) (g : ordinal_map n k)
    (y : simplex X m) (z : simplex X k)
    (e : simplex_map X f y = simplex_map X g z)
    (j : ordinal_map m n)
    (hj : ordinal_map_compose j f = ordinal_map_identity m) :
  simplex_map X (ordinal_map_compose j g) z = y.
Proof.
  rewrite simplex_map_compose. rewrite <- e.
  rewrite <- simplex_map_compose. rewrite hj simplex_map_identity. reflexivity.
Qed.

Theorem nondegenerate_core_least_dimension (X : simplicial_set) n m k
    (f : ordinal_map n m) (hf : ordinal_surjective f)
    (g : ordinal_map n k) (y : simplex X m) (z : simplex X k)
    (hy : nondegenerate X y)
    (e : simplex_map X f y = simplex_map X g z) : (m <= k)%N.
Proof.
  have h := @core_section_pullback X n m k f g y z e
    (ordinal_section hf) (ordinal_section_right_inverse hf).
  apply (@ordinal_injective_dimension m k
    (ordinal_map_compose (ordinal_section hf) g)).
  apply (@nondegenerate_pullback_injective X m k _ z). rewrite h. exact hy.
Qed.

Theorem nondegenerate_core_dimensions_equal (X : simplicial_set) n m k
    (f : ordinal_map n m) (hf : ordinal_surjective f)
    (g : ordinal_map n k) (hg : ordinal_surjective g)
    (y : simplex X m) (z : simplex X k)
    (hy : nondegenerate X y) (hz : nondegenerate X z)
    (e : simplex_map X f y = simplex_map X g z) : m = k.
Proof.
  apply/eqP. rewrite eqn_leq. apply/andP. split.
  - exact (@nondegenerate_core_least_dimension X n m k f hf g y z hy e).
  - exact (@nondegenerate_core_least_dimension X n k m g hg f z y hz (esym e)).
Qed.

Lemma nondegenerate_core_section_identity (X : simplicial_set) n m
    (f g : ordinal_map n m) (y z : simplex X m)
    (hy : nondegenerate X y)
    (e : simplex_map X f y = simplex_map X g z)
    (j : ordinal_map m n)
    (hj : ordinal_map_compose j f = ordinal_map_identity m) :
  ordinal_map_compose j g = ordinal_map_identity m.
Proof.
  apply ordinal_injective_self_identity.
  apply (@nondegenerate_pullback_injective X m m _ z).
  rewrite (@core_section_pullback X n m m f g y z e j hj). exact hy.
Qed.

Theorem nondegenerate_core_same_dimension_unique (X : simplicial_set) n m
    (f : ordinal_map n m) (hf : ordinal_surjective f)
    (g : ordinal_map n m) (y z : simplex X m)
    (hy : nondegenerate X y)
    (e : simplex_map X f y = simplex_map X g z) : f = g /\ y = z.
Proof.
  have hfg : f = g.
  { apply ordinal_map_ext. intro x.
    have h := @nondegenerate_core_section_identity X n m f g y z hy e
      (ordinal_section_through hf x) (ordinal_section_through_right_inverse hf x).
    have hx := f_equal (fun q : ordinal_map m m => q (f x)) h.
    change (g (ordinal_section_through hf x (f x)) = f x) in hx.
    rewrite ordinal_section_through_point in hx. symmetry. exact hx. }
  split; first exact hfg.
  have h := @core_section_pullback X n m m f g y z e
    (ordinal_section hf) (ordinal_section_right_inverse hf).
  rewrite <- hfg in h. rewrite ordinal_section_right_inverse simplex_map_identity in h.
  symmetry. exact h.
Qed.

(** Dimensions, surjections, and core simplices are all unique. The two explicit
    transports keep the statement meaningful before the dimension equality is
    eliminated; no equality of arbitrary different simplex types is asserted. *)
Theorem nondegenerate_core_unique (X : simplicial_set) n m k
    (f : ordinal_map n m) (hf : ordinal_surjective f)
    (g : ordinal_map n k) (hg : ordinal_surjective g)
    (y : simplex X m) (z : simplex X k)
    (hy : nondegenerate X y) (hz : nondegenerate X z)
    (e : simplex_map X f y = simplex_map X g z) :
  exists d : m = k,
    eq_rect m (fun t => ordinal_map n t) f k d = g /\
    eq_rect m (simplex X) y k d = z.
Proof.
  have d := @nondegenerate_core_dimensions_equal X n m k f hf g hg y z hy hz e.
  subst k. exists (Logic.eq_refl m). cbn.
  exact (@nondegenerate_core_same_dimension_unique X n m f hf g y z hy e).
Qed.

End DPSimplicialNondegenerateUniqueness.
