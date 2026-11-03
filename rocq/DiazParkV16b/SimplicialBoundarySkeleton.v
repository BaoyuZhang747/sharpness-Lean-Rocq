(** The actual boundary of Delta[d] is generated strictly below dimension d. *)
From mathcomp Require Import all_ssreflect order boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplexCategoryFactorization SimplexCategoryFactorizationSections SimplexCategoryFactorizationProperties
 SimplicialSet SimplicialSetYoneda SimplicialSubcomplex SimplicialSubcomplexGenerated SimplicialBoundary SimplicialSkeletonAttachmentStages.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module DPSimplicialBoundarySkeleton.
Import DPSimplicialTypes DPSimplexCategory DPSimplexFactorization DPSimplexSections DPSimplexFactorizationProperties
 DPSimplicialSet DPSimplicialYoneda DPSimplicialSubcomplex DPSimplicialGenerated DPSimplicialBoundary DPSimplicialAttachmentStages.

Lemma boundary_injection_nonsurjective d k (f:ordinal_map k d)
 (hf:~ordinal_surjective f) : ~ordinal_surjective (image_injection f).
Proof.
move=>hi; apply hf; rewrite -(image_factorization f).
apply ordinal_compose_surjective; [exact (@image_surjection_surjective k d f) | exact hi].
Qed.

Theorem boundary_skeletal_stage_member d k (x:simplex (boundary_set d) k) :
 member (skeletal_stage (boundary_set d) d) k x.
Proof.
case: x=>f hf.
exists (ordinal_image_dimension f),
 (exist _ (image_injection f) (@boundary_injection_nonsurjective d k f hf)),
 (image_surjection f).
split; first exact: nonsurjective_image_dimension_lt.
apply subcomplex_simplex_ext; exact: image_factorization.
Qed.

Theorem boundary_skeletal_stage_top d : skeletal_stage (boundary_set d) d=subcomplex_top (boundary_set d).
Proof.
apply subcomplex_ext=>k x; split; first by move=>_; exact I.
move=>_; exact: boundary_skeletal_stage_member.
Qed.

Definition boundary_skeletal_lift d : simplicial_map (boundary_set d)
 (subcomplex_set (skeletal_stage (boundary_set d) d)).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category (boundary_set d)
 (subcomplex_set (skeletal_stage (boundary_set d) d))
 (fun k x=>exist _ x (@boundary_skeletal_stage_member d k x)) _).
move=>k m f; apply type_morphism_ext=>x; apply subcomplex_simplex_ext; reflexivity.
Defined.

Lemma boundary_skeletal_lift_inclusion d : nat_comp (boundary_skeletal_lift d)
 (subcomplex_inclusion (skeletal_stage (boundary_set d) d))=nat_id (boundary_set d).
Proof. apply nat_trans_ext=>k; reflexivity. Qed.
Lemma boundary_skeletal_inclusion_lift d : nat_comp
 (subcomplex_inclusion (skeletal_stage (boundary_set d) d)) (boundary_skeletal_lift d)=
 nat_id (subcomplex_set (skeletal_stage (boundary_set d) d)).
Proof.
apply nat_trans_ext=>k; apply type_morphism_ext=>x; apply subcomplex_simplex_ext; reflexivity.
Qed.
Definition boundary_skeletal_isomorphism d : @isomorphism simplicial_category
 (subcomplex_set (skeletal_stage (boundary_set d) d)) (boundary_set d) :=
 @Build_isomorphism simplicial_category _ _ (subcomplex_inclusion (skeletal_stage (boundary_set d) d))
 (boundary_skeletal_lift d) (boundary_skeletal_inclusion_lift d) (boundary_skeletal_lift_inclusion d).
End DPSimplicialBoundarySkeleton.
