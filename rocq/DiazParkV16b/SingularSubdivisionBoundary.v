(** Signed barycentric subdivision commutes with the actual singular boundary. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical all_fingroup.
From mathcomp Require Import reals topology.
From DiazPark Require Import BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplicialSet SimplicialSetOperators SimplicialChains
  SimplexCategoryIdentities SingularSet SingularSubdivisionOperators SingularSubdivisionCellFaces
  SubdivisionPermutationSigns SubdivisionPermutationAdjacent SubdivisionPermutationOuter
  SubdivisionPermutationOuterFaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPSimplexIdentities DPSimplicialOperators
  DPSingularSet DPSingularSubdivision DPSingularSubdivisionCellFaces
  DPSubdivisionPermutationSigns DPSubdivisionPermutationAdjacent DPSubdivisionPermutationOuter
  DPSubdivisionPermutationOuterFaces DPSimplicialChains.
Local Open Scope ring_scope.

Module DPSingularSubdivisionBoundary.
Section Boundary.
Variable Real : realType.
Variable R : pzRingType.
Variable X : topologicalType.
Let S := singular_set Real X.

Lemma boundary_basis_faces n (s : DPSimplicialSet.simplex S n.+1) :
  @boundary R S n (free_basis R s) =
    \sum_(i : 'I_n.+2) (-1 : R)^+(val i) *: free_basis R (face S i s).
Proof.
rewrite /boundary; apply eq_bigr => i _; rewrite /face_map free_map_basis /indexed_face.
have e : (inord (val i) : 'I_n.+2) = i by apply val_inj; apply inordK; exact: ltn_ord.
by rewrite e.
Qed.

Lemma subdivision_internal_sum_zero n (j : 'I_n.+1)
    (s : DPSimplicialSet.simplex S n.+1) :
  \sum_(p : {perm 'I_n.+2}) permutation_sign R p *:
    free_basis R (face S (vertex_widen j) (singular_barycentric_cell p s)) = 0.
Proof.
apply: (@adjacent_invariant_sum_zero n j R (term R S n)) => p.
by rewrite singular_barycentric_cell_internal_face.
Qed.

Lemma subdivision_outer_face n (c : 'I_n.+2) (q : {perm 'I_n.+1})
    (s : DPSimplicialSet.simplex S n.+1) :
  face S ord_max (singular_barycentric_cell (outer_assemble c q) s) =
    singular_barycentric_cell q (face S c s).
Proof. apply singular_barycentric_cell_outer_face => k; exact: outer_assemble_coface. Qed.

Lemma subdivision_boundary_outer_sum n (s : DPSimplicialSet.simplex S n.+1) :
  @boundary R S n (subdivision_at Real R X n.+1 (free_basis R s)) =
    \sum_(p : {perm 'I_n.+2}) (permutation_sign R p * (-1 : R)^+n.+1) *:
      free_basis R (face S ord_max (singular_barycentric_cell p s)).
Proof.
rewrite subdivision_at_basis linear_sum.
transitivity (\sum_(p : {perm 'I_n.+2})
  ((\sum_(j : 'I_n.+1) permutation_sign R p *: ((-1 : R)^+(val j) *:
    free_basis R (face S (vertex_widen j) (singular_barycentric_cell p s)))) +
  (permutation_sign R p * (-1 : R)^+n.+1) *:
    free_basis R (face S ord_max (singular_barycentric_cell p s)))).
- apply eq_bigr => p _; rewrite linearZ.
  change (permutation_sign R p *: @boundary R S n (free_basis R (singular_barycentric_cell p s)) =
    (\sum_(j : 'I_n.+1) permutation_sign R p *: ((-1 : R)^+(val j) *:
      free_basis R (face S (vertex_widen j) (singular_barycentric_cell p s)))) +
    (permutation_sign R p * (-1 : R)^+n.+1) *:
      free_basis R (face S ord_max (singular_barycentric_cell p s))).
  rewrite boundary_basis_faces big_ord_recr scalerDr scaler_sumr.
  congr (_ + _).
  + apply eq_bigr => j _.
    have e : widen_ord (leqnSn n.+1) j = vertex_widen j by apply val_inj.
    by rewrite e.
  + by rewrite scalerA.
- rewrite big_split exchange_big.
  have hz : \sum_(j : 'I_n.+1) \sum_(p : {perm 'I_n.+2})
      permutation_sign R p *: ((-1 : R)^+(val j) *:
        free_basis R (face S (vertex_widen j) (singular_barycentric_cell p s))) = 0.
    apply: big1 => j _.
    transitivity ((-1 : R)^+(val j) *:
      \sum_(p : {perm 'I_n.+2}) permutation_sign R p *:
        free_basis R (face S (vertex_widen j) (singular_barycentric_cell p s))).
    + rewrite scaler_sumr; apply eq_bigr => p _.
      by rewrite !scalerA commr_sign.
    + by rewrite subdivision_internal_sum_zero scaler0.
  rewrite hz; exact: add0r.
Qed.

Lemma subdivision_boundary_basis n (s : DPSimplicialSet.simplex S n.+1) :
  @boundary R S n (subdivision_at Real R X n.+1 (free_basis R s)) =
    subdivision_at Real R X n (@boundary R S n (free_basis R s)).
Proof.
rewrite subdivision_boundary_outer_sum outer_signed_reindex boundary_basis_faces linear_sum.
apply eq_bigr => c _; rewrite linearZ.
change ((\sum_(q : {perm 'I_n.+1}) ((-1 : R)^+(val c) * permutation_sign R q) *:
    free_basis R (face S ord_max (singular_barycentric_cell (outer_assemble c q) s))) =
  (-1 : R)^+(val c) *: subdivision_at Real R X n (free_basis R (face S c s))).
rewrite subdivision_at_basis scaler_sumr.
apply eq_bigr => q _; by rewrite subdivision_outer_face scalerA.
Qed.

Theorem subdivision_boundary n (a : term R S n.+1) :
  @boundary R S n (subdivision_at Real R X n.+1 a) =
    subdivision_at Real R X n (@boundary R S n a).
Proof.
apply (free_lift_ext
  (g := (@boundary R S n \o (subdivision_at Real R X n.+1 : {linear _ -> _}) : {linear _ -> _}))
  (h := ((subdivision_at Real R X n : {linear _ -> _}) \o @boundary R S n : {linear _ -> _}))).
exact: subdivision_boundary_basis.
Qed.

Definition subdivision_chain_map : DPChainComplex.chain_map (chains R S) (chains R S) :=
  @DPChainComplex.ChainMap R (chains R S) (chains R S)
    (fun n => (subdivision_at Real R X n : {linear _ -> _})) subdivision_boundary.

Lemma subdivision_chain_map_degree_zero (a : term R S 0) :
  DPChainComplex.chain_map_at subdivision_chain_map 0 a = a.
Proof. exact: subdivision_degree_zero. Qed.

End Boundary.
End DPSingularSubdivisionBoundary.









