(** Native unnormalized category-nerve chains: free modules on all composable
    strings with the alternating actual face boundary. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category BarPaths BarFreeModule BarAlternating.
From DiazParkV16b Require Import ChainComplex CategoryBarPullbackPaths.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkFreeModule DiazParkBarAlternating
  DPChainComplex DPCategoryBarPullback.
Local Open Scope ring_scope.

Section Strings.
Variable R : pzRingType.
Variable C : category.

Definition category_string_term n : lmodType R := free_module R (@path C n).
Definition category_string_face n i :
    {linear category_string_term n.+1 -> category_string_term n} :=
  free_map R (@path_face C n i).

Definition category_string_boundary n (a : category_string_term n.+1) : category_string_term n :=
  \sum_(i < n.+2) (-1) ^+ i *: category_string_face n i a.

Arguments category_string_boundary n a : clear implicits.

Lemma category_string_boundary_linear n : linear (@category_string_boundary n).
Proof.
intros r a b; rewrite /category_string_boundary scaler_sumr -big_split.
apply eq_bigr; intros i _.
by rewrite linearP scalerDr !scalerA commr_sign.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (category_string_term n.+1)
  (category_string_term n) _ (@category_string_boundary n) (@category_string_boundary_linear n).

Lemma category_string_faces n i j (a : category_string_term n.+2) :
    (i <= j)%coq_nat -> (j <= n.+1)%coq_nat ->
    category_string_face n j (category_string_face n.+1 i a) =
    category_string_face n i (category_string_face n.+1 j.+1 a).
Proof.
intros hij hj.
apply (free_lift_ext
  (g := (category_string_face n j \o category_string_face n.+1 i : {linear _ -> _}))
  (h := (category_string_face n i \o category_string_face n.+1 j.+1 : {linear _ -> _}))).
intro s; rewrite /= /category_string_face !free_map_basis.
by rewrite (@path_faces C n i j s hij hj).
Qed.

Theorem category_string_boundary_squared n (a : category_string_term n.+2) :
    category_string_boundary n (category_string_boundary n.+1 a) = 0.
Proof.
rewrite /category_string_boundary.
transitivity (\sum_(j < n.+3) \sum_(i < n.+2)
  (-1) ^+ j *: ((-1) ^+ i *:
    category_string_face n i (category_string_face n.+1 j a))).
- rewrite [RHS]exchange_big.
  apply eq_bigr; intros i _; rewrite linear_sum scaler_sumr.
  apply eq_bigr; intros j _.
  by rewrite linearZ !scalerA (commr_sign ((-1) ^+ i) j).
- apply (@alternating_rectangle_zero R (category_string_term n) n.+2
    (fun i j => category_string_face n j (category_string_face n.+1 i a))).
  move=> i j /leP hij hj.
  have hj' : (j <= n.+1)%coq_nat by apply/leP; exact: hj.
  exact: category_string_faces.
Qed.

Definition category_string_chain : chain_complex R :=
  @ChainComplex R category_string_term
    (fun n => (@category_string_boundary n : {linear _ -> _})) category_string_boundary_squared.

Definition category_string_augmentation : {linear category_string_term 0%N -> R^o} :=
  (free_lift (fun _ : @path C 0%N => (1 : R^o)) : {linear _ -> _}).

Lemma category_string_augmentation_basis (s : @path C 0%N) :
    category_string_augmentation (free_basis R s) = 1.
Proof. exact: free_lift_basis. Qed.

Theorem category_string_augmentation_boundary (a : category_string_term 1%N) :
    category_string_augmentation (category_string_boundary 0%N a) = 0.
Proof.
pose f : {linear category_string_term 1%N -> R^o} :=
  (category_string_augmentation \o @category_string_boundary 0%N : {linear _ -> _}).
change (f a = 0).
rewrite -[in LHS](free_basis_generation a) linear_sum.
apply big1_seq; intros s _; rewrite linearZ.
suff hz : f (free_basis R s) = 0 by rewrite hz; exact: scaler0.
change (category_string_augmentation (category_string_boundary 0%N (free_basis R s)) = 0).
rewrite /category_string_boundary !big_ord_recl big_ord0 /=.
rewrite !linearD !linearZ linear0 /category_string_face !free_map_basis
  !category_string_augmentation_basis.
change ((-1 : R) ^+ 0 *: (1 : R^o) +
  ((-1 : R) ^+ 1 *: (1 : R^o) + 0) = 0).
by rewrite expr0 expr1 scale1r scaleN1r addr0 subrr.
Qed.
End Strings.

Arguments category_string_term R C n.
Arguments category_string_chain R C.
Arguments category_string_augmentation R C.
