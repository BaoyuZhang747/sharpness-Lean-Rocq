(** Unnormalized chains of actual simplicial sets, over arbitrary rings. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category BarFreeModule BarAlternating.
From DiazParkV16b Require Import ChainComplex SimplexCategoryIdentities
  SimplicialSet SimplicialSetOperators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DiazParkBarAlternating DPChainComplex
  DPSimplicialSet DPSimplicialOperators DPSimplexIdentities.
Local Open Scope ring_scope.

Module DPSimplicialChains.
Section Chains.
Variable R : pzRingType.
Variable X : simplicial_set.

Definition term n : lmodType R := free_module R (simplex X n).
Definition indexed_face n i : simplex X n.+1 -> simplex X n :=
  face X (inord i).
Arguments indexed_face n i x : clear implicits.

Lemma indexed_faces n i j (x : simplex X n.+2) :
  (i <= j)%N -> (j < n.+2)%N ->
  indexed_face n j (indexed_face n.+1 i x) =
    indexed_face n i (indexed_face n.+1 j.+1 x).
Proof.
move=> hij hj.
have hi : (i < n.+2)%N := leq_ltn_trans hij hj.
have hi' : (i < n.+3)%N := ltn_trans hi (ltnSn _).
have hj' : (j.+1 < n.+3)%N := hj.
have ei : (inord i : 'I_n.+2) = Ordinal hi by apply val_inj; exact: inordK.
have ej : (inord j : 'I_n.+2) = Ordinal hj by apply val_inj; exact: inordK.
have ew : (inord i : 'I_n.+3) = vertex_widen (Ordinal hi).
  apply val_inj; exact: inordK.
have es : (inord j.+1 : 'I_n.+3) = vertex_successor (Ordinal hj).
  apply val_inj; exact: inordK.
rewrite /indexed_face ei ej ew es.
exact (@face_face X n (Ordinal hi) (Ordinal hj) x hij).
Qed.

Definition face_map n i : {linear term n.+1 -> term n} :=
  free_map R (@indexed_face n i).

Definition boundary n (a : term n.+1) : term n :=
  \sum_(i < n.+2) (-1) ^+ i *: face_map n i a.
Arguments boundary n a : clear implicits.

Lemma boundary_linear n : linear (@boundary n).
Proof.
move=> r a b; rewrite /boundary scaler_sumr -big_split.
apply eq_bigr => i _.
by rewrite linearP scalerDr !scalerA commr_sign.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (term n.+1) (term n) _
  (@boundary n) (@boundary_linear n).

Lemma face_maps n i j (a : term n.+2) :
  (i <= j)%N -> (j < n.+2)%N ->
  face_map n j (face_map n.+1 i a) = face_map n i (face_map n.+1 j.+1 a).
Proof.
move=> hij hj.
apply (free_lift_ext
  (g := (face_map n j \o face_map n.+1 i : {linear _ -> _}))
  (h := (face_map n i \o face_map n.+1 j.+1 : {linear _ -> _}))).
move=> x; rewrite /= /face_map !free_map_basis.
by rewrite indexed_faces.
Qed.

Theorem boundary_squared n (a : term n.+2) : boundary n (boundary n.+1 a) = 0.
Proof.
rewrite /boundary.
transitivity (\sum_(j < n.+3) \sum_(i < n.+2)
  (-1) ^+ j *: ((-1) ^+ i *: face_map n i (face_map n.+1 j a))).
- rewrite [RHS]exchange_big.
  apply eq_bigr => i _; rewrite linear_sum scaler_sumr.
  apply eq_bigr => j _.
  by rewrite linearZ !scalerA (commr_sign ((-1) ^+ i) j).
- apply (@alternating_rectangle_zero R (term n) n.+2
    (fun i j => face_map n j (face_map n.+1 i a))).
  move=> i j hij hj; exact (@face_maps n i j a hij hj).
Qed.

Definition chains : chain_complex R :=
  @ChainComplex R term (fun n => (@boundary n : {linear _ -> _})) boundary_squared.

Definition augmentation : {linear term 0%N -> R^o} :=
  (free_lift (fun _ : simplex X 0%N => (1 : R^o)) : {linear _ -> _}).

Lemma augmentation_basis (x : simplex X 0%N) : augmentation (free_basis R x) = 1.
Proof. exact: free_lift_basis. Qed.

Theorem augmentation_boundary (a : term 1%N) : augmentation (boundary 0%N a) = 0.
Proof.
pose f : {linear term 1%N -> R^o} := (augmentation \o @boundary 0%N : {linear _ -> _}).
change (f a = 0).
rewrite -[in LHS](free_basis_generation a) linear_sum.
apply big1_seq => x _; rewrite linearZ.
suff hz : f (free_basis R x) = 0 by rewrite hz; exact: scaler0.
change (augmentation (boundary 0%N (free_basis R x)) = 0).
rewrite /boundary !big_ord_recl big_ord0 /=.
rewrite !linearD !linearZ linear0 /face_map !free_map_basis !augmentation_basis.
change ((-1 : R) ^+ 0 *: (1 : R^o) +
  ((-1 : R) ^+ 1 *: (1 : R^o) + 0) = 0).
by rewrite expr0 expr1 scale1r scaleN1r addr0 subrr.
Qed.
End Chains.
End DPSimplicialChains.
