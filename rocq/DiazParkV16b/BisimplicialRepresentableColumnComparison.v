(** The actual representable bicomplex maps to the zeroth-row simplex complex by vertical augmentation. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators SimplicialSet SimplicialChains SimplicialChainsMaps ChainComplex
  ChainQuasiIsomorphism AugmentedModuleChainComparison BisimplicialSet BisimplicialChains
  BisimplicialRepresentable BisimplicialRepresentableColumnContraction
  FirstQuadrantChainBicomplex FirstQuadrantChainTotal FirstQuadrantChainTotalMaps
  FirstQuadrantChainRowZero FirstQuadrantChainComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPSimplexCategory DPSimplicialSet DPSimplicialChains
  DPChainComplex DPChainQuasiIsomorphism DPAugmentedModuleChainComparison DPBisimplicialSet
  DPBisimplicialChains DPBisimplicialRepresentable DPBisimplicialRepresentableColumnContraction
  DPFirstQuadrantChain DPFirstQuadrantChainTotal DPFirstQuadrantChainTotalMaps
  DPFirstQuadrantChainRowZero DPFirstQuadrantChainComparison.
Local Open Scope ring_scope.

Module DPBisimplicialRepresentableColumnComparison.
Section Model.
Variable R : pzRingType.
Variables m n : nat.
Let X := representable m n.
Let K := bisimplicial_bicomplex R X.
Let C := chains R (standard_simplex m).
Let L := row_zero C.
Definition column_comparison_at p q : {linear bicomplex_term K p q -> bicomplex_term L p q} :=
  match q as k return {linear bicomplex_term K p k -> bicomplex_term L p k} with
  | 0%N => column_augmentation m n p R
  | k.+1 => (@zero_map R (bicomplex_term K p k.+1) (zero_module R) : {linear _ -> _})
  end.

Lemma column_augmentation_horizontal_face p i (a : bi_term R X p.+1 0%N) :
  face_map R (standard_simplex m) p i (column_augmentation m n p.+1 R a) =
    column_augmentation m n p R (DPSimplicialChainMaps.map_at R (fmap X (DPSimplexOperators.coface (inord i))) 0 a).
Proof.
apply: (free_lift_ext
  (g := (face_map R (standard_simplex m) p i \o column_augmentation m n p.+1 R : {linear _ -> _}))
  (h := (column_augmentation m n p R \o DPSimplicialChainMaps.map_at R (fmap X (DPSimplexOperators.coface (inord i))) 0 : {linear _ -> _}))).
move=> [u v]; rewrite /= /face_map /column_augmentation /DPSimplicialChainMaps.map_at !free_map_basis; reflexivity.
Qed.
Lemma column_comparison_horizontal p q a :
  horizontal L p q (column_comparison_at p.+1 q a) =
    column_comparison_at p q (horizontal K p q a).
Proof.
case: q a => [|q] a; last reflexivity.
change (@DPSimplicialChains.boundary R (standard_simplex m) p (column_augmentation m n p.+1 R a) =
  column_augmentation m n p R (@horizontal_d R X p 0 a)).
rewrite /DPSimplicialChains.boundary /horizontal_d linear_sum; apply eq_bigr => i _.
rewrite linearZ; congr (_ *: _); exact: column_augmentation_horizontal_face.
Qed.
Lemma column_comparison_vertical p q a :
  vertical L p q (column_comparison_at p q.+1 a) =
    column_comparison_at p q (vertical K p q a).
Proof.
case: q a => [|q] a; last reflexivity.
change (0 = column_augmentation m n p R (@DPSimplicialChains.boundary R (representable_row m n p) 0 a)).
symmetry; exact: column_augmentation_boundary.
Qed.
Definition column_comparison : bicomplex_map K L :=
  @BicomplexMap R K L column_comparison_at column_comparison_horizontal column_comparison_vertical.

Theorem column_comparison_quasi_isomorphism p : quasi_isomorphism (vertical_map column_comparison p).
Proof.
apply (@augmented_comparison_quasi_isomorphism R (term R (standard_simplex m) p)
  (vertical_complex K p) (vertical_complex L p) (vertical_map column_comparison p)
  (column_augmentation m n p R) (idfun : {linear term R (standard_simplex m) p -> _})).
- move=> x; reflexivity.
- move=> x; reflexivity.
- move=> a; exists (column_augmentation_section m n p R a); exact: column_augmentation_sectionK.
- move=> x hx; exact: representable_column_augmentation_exact hx.
- move=> x hx; exists 0; change (0 = x); exact: esym hx.
- move=> q x hx; exact: representable_column_positive_exact hx.
- move=> q x _; exists 0; change (0 = x); symmetry; exact: zero_module_unique.
Qed.
Theorem column_total_comparison_quasi_isomorphism : quasi_isomorphism (total_map column_comparison).
Proof. exact: total_map_quasi_isomorphism column_comparison_quasi_isomorphism. Qed.
End Model.
End DPBisimplicialRepresentableColumnComparison.
