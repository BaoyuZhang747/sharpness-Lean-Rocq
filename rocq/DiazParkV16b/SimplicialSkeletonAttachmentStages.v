From mathcomp Require Import all_ssreflect order boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory
  SimplexCategoryFactorization SimplexCategoryFactorizationSections
  SimplexCategoryFactorizationProperties SimplicialSet SimplicialSetYoneda
  SimplicialSubcomplex SimplicialSubcomplexGenerated SimplicialSkeleton
  SimplicialNondegenerate SimplicialNondegenerateUniqueness
  SimplicialNondegenerateSkeleton SimplicialBoundary.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialAttachmentStages.
Import DPSimplicialTypes DPSimplexCategory DPSimplexFactorization DPSimplexSections
  DPSimplexFactorizationProperties DPSimplicialSet DPSimplicialYoneda
  DPSimplicialSubcomplex DPSimplicialGenerated DPSimplicialSkeleton
  DPSimplicialNondegenerate DPSimplicialNondegenerateUniqueness
  DPSimplicialNondegenerateSkeleton DPSimplicialBoundary.

(** Stage n contains the simplices generated in dimensions strictly below n.
    Thus stage zero is empty and stage (n+1) is the inclusive n-skeleton. *)
Definition skeletal_stage (X : simplicial_set) n : subcomplex X :=
  generated_subcomplex (fun k (_ : simplex X k) => (k < n)%N).

Lemma skeletal_stage_zero X : skeletal_stage X 0 = subcomplex_bottom X.
Proof.
  apply subcomplex_ext. intros k x. split.
  - intros [m [y [f [hm _]]]]. by rewrite ltn0 in hm.
  - intro h. contradiction.
Qed.

Lemma skeletal_stage_succ X n : skeletal_stage X n.+1 = skeleton X n.
Proof. reflexivity. Qed.

Lemma skeletal_stage_mono X n :
  subcomplex_le (skeletal_stage X n) (skeletal_stage X n.+1).
Proof.
  apply generated_mono. intros k x h. exact (ltn_trans h (ltnSn n)).
Qed.

Lemma core_skeletal_stage_iff X r n m (q : ordinal_map n m)
    (hq : ordinal_surjective q) (y : simplex X m) (hy : nondegenerate X y) :
  member (skeletal_stage X r) n (simplex_map X q y) <-> (m < r)%N.
Proof.
  split.
  - intros [k [z [g [hk he]]]]. exact (leq_ltn_trans
      (@nondegenerate_core_least_dimension X n m k q hq g y z hy (esym he)) hk).
  - intro h. exists m, y, q. split; [exact h|reflexivity].
Qed.

Lemma boundary_characteristic_below X n k (x : simplex X n) (f : ordinal_map k n)
    (hf : ~ ordinal_surjective f) :
  member (skeletal_stage X n) k (simplex_map X f x).
Proof.
  exists (ordinal_image_dimension f), (simplex_map X (image_injection f) x),
    (image_surjection f). split.
  - exact (nonsurjective_image_dimension_lt hf).
  - rewrite <- simplex_map_compose. rewrite image_factorization. reflexivity.
Qed.

Lemma nondegenerate_characteristic_below_iff X n k (x : simplex X n)
    (hx : nondegenerate X x) (f : ordinal_map k n) :
  member (skeletal_stage X n) k (simplex_map X f x) <-> ~ ordinal_surjective f.
Proof.
  split; last exact (@boundary_characteristic_below X n k x f).
  intros h hf. have hlt := proj1 (@core_skeletal_stage_iff X n k n f hf x hx) h.
  by rewrite ltnn in hlt.
Qed.

Definition nondegenerate_cell (X : simplicial_set) n :=
  {x : simplex X n | nondegenerate X x}.

Lemma characteristic_next_stage X n k (x : simplex X n) (f : ordinal_map k n) :
  member (skeletal_stage X n.+1) k (simplex_map X f x).
Proof. exists n, x, f. split; [exact (ltnSn n)|reflexivity]. Qed.

Definition cell_characteristic X n (x : nondegenerate_cell X n) :
    simplicial_map (standard_simplex n) (subcomplex_set (skeletal_stage X n.+1)).
Proof.
  refine (@Build_nat_trans (opposite simplex_category) type_category
    (standard_simplex n) (subcomplex_set (skeletal_stage X n.+1))
    (fun k f => exist _ (simplex_map X f (proj1_sig x))
      (@characteristic_next_stage X n k (proj1_sig x) f)) _).
  intros k m f. apply type_morphism_ext. intro g.
  apply subcomplex_simplex_ext. apply simplex_map_compose.
Defined.

Definition cell_boundary_characteristic X n (x : nondegenerate_cell X n) :
    simplicial_map (boundary_set n) (subcomplex_set (skeletal_stage X n)).
Proof.
  refine (@Build_nat_trans (opposite simplex_category) type_category
    (boundary_set n) (subcomplex_set (skeletal_stage X n))
    (fun k f => exist _ (simplex_map X (proj1_sig f) (proj1_sig x))
      (@boundary_characteristic_below X n k (proj1_sig x) (proj1_sig f) (proj2_sig f))) _).
  intros k m f. apply type_morphism_ext. intro g.
  apply subcomplex_simplex_ext. apply simplex_map_compose.
Defined.

Lemma cell_boundary_square X n (x : nondegenerate_cell X n) :
  nat_comp (cell_boundary_characteristic x) (subcomplex_map (@skeletal_stage_mono X n)) =
  nat_comp (boundary_inclusion n) (cell_characteristic x).
Proof. apply nat_trans_ext. intro k. apply type_morphism_ext. intro f.
  apply subcomplex_simplex_ext. reflexivity. Qed.

End DPSimplicialAttachmentStages.
