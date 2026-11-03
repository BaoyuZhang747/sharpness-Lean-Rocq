(** Actual augmented contraction of the diagonal of a bisimplicial representable. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import SimplexCategory SimplicialSet SimplicialChains ChainComplex
  BisimplicialSet BisimplicialChains BisimplicialRepresentable StandardSimplexCone
  StandardSimplexConeChains SimplicialConeContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPSimplexCategory DPSimplicialSet DPSimplicialChains
  DPChainComplex DPBisimplicialSet DPBisimplicialChains DPBisimplicialRepresentable
  DPStandardSimplexCone DPStandardSimplexConeChains DPSimplicialConeContraction.
Local Open Scope ring_scope.

Module DPBisimplicialRepresentableDiagonalContraction.
Section Model.
Variables m n : nat.
Let X := diagonal (representable m n).
Definition diagonal_cone q (x : simplex X q) : simplex X q.+1 := (cone x.1, cone x.2).
Lemma diagonal_cone_zero q x : @indexed_face X q 0 (diagonal_cone x) = x.
Proof.
case: x => a b.
change ((@indexed_face (standard_simplex m) q 0 (cone a),
  @indexed_face (standard_simplex n) q 0 (cone b)) = (a,b)).
by rewrite !indexed_cone_zero.
Qed.
Lemma diagonal_cone_successor q (i : 'I_q.+2) x :
  @indexed_face X q.+1 i.+1 (diagonal_cone x) = diagonal_cone (@indexed_face X q i x).
Proof.
case: x => a b.
change ((@indexed_face (standard_simplex m) q.+1 i.+1 (cone a),
  @indexed_face (standard_simplex n) q.+1 i.+1 (cone b)) =
  (cone (@indexed_face (standard_simplex m) q i a), cone (@indexed_face (standard_simplex n) q i b))).
by rewrite !indexed_cone_successor.
Qed.
Definition diagonal_vertex : simplex X 0 := (zero_vertex m, zero_vertex n).
Lemma diagonal_cone_last x : @indexed_face X 0 1 (diagonal_cone x) = diagonal_vertex.
Proof.
case: x => a b.
change ((@indexed_face (standard_simplex m) 0 1 (cone a),
  @indexed_face (standard_simplex n) 0 1 (cone b)) = (zero_vertex m,zero_vertex n)).
by rewrite !indexed_cone_last_zero.
Qed.

Variable R : pzRingType.
Definition diagonal_cone_map q : {linear term R X q -> term R X q.+1} :=
  @DPSimplicialConeContraction.cone_map R X (@diagonal_cone) q.
Definition diagonal_augmentation_section (r : R^o) : term R X 0 := (r : R) *: free_basis R diagonal_vertex.
Lemma diagonal_augmentation_section_linear : linear diagonal_augmentation_section.
Proof. move=> a x y; by rewrite /diagonal_augmentation_section scalerDl scalerA. Qed.
HB.instance Definition _ := GRing.isLinear.Build R _ _ _
  diagonal_augmentation_section diagonal_augmentation_section_linear.
Lemma diagonal_augmentation_sectionK r : augmentation R X (diagonal_augmentation_section r) = r.
Proof. rewrite /diagonal_augmentation_section linearZ augmentation_basis; exact: mulr1. Qed.
Lemma diagonal_cone_last_basis x :
  free_basis R (@indexed_face X 0 1 (diagonal_cone x)) =
    diagonal_augmentation_section (augmentation R X (free_basis R x)).
Proof. by rewrite diagonal_cone_last augmentation_basis /diagonal_augmentation_section scale1r. Qed.
Theorem diagonal_contraction_successor q (a : term R X q.+1) :
  @DPSimplicialChains.boundary R X q.+1 (diagonal_cone_map q.+1 a) +
    diagonal_cone_map q (@DPSimplicialChains.boundary R X q a) = a.
Proof. exact (@cone_contraction_successor R X (@diagonal_cone)
  diagonal_cone_zero diagonal_cone_successor q a). Qed.
Theorem diagonal_contraction_zero (a : term R X 0) :
  @DPSimplicialChains.boundary R X 0 (diagonal_cone_map 0 a) +
    diagonal_augmentation_section (augmentation R X a) = a.
Proof. exact (@cone_contraction_zero R X (@diagonal_cone) diagonal_cone_zero
  R^o (augmentation R X) diagonal_augmentation_section diagonal_cone_last_basis a). Qed.
Theorem representable_diagonal_positive_exact q (a : chain_term (diagonal_chains R (representable m n)) q.+1) :
  @cycle R (diagonal_chains R (representable m n)) q.+1 a ->
  @DPChainComplex.boundary R (diagonal_chains R (representable m n)) q.+1 a.
Proof. exact (@cone_positive_exact R X (@diagonal_cone) diagonal_cone_zero diagonal_cone_successor q a). Qed.
Theorem representable_diagonal_augmentation_exact (a : term R X 0) :
  augmentation R X a = 0 -> @DPChainComplex.boundary R (diagonal_chains R (representable m n)) 0 a.
Proof. exact (@cone_augmentation_exact R X (@diagonal_cone) diagonal_cone_zero
  R^o (augmentation R X) diagonal_augmentation_section diagonal_cone_last_basis a). Qed.
End Model.
End DPBisimplicialRepresentableDiagonalContraction.
