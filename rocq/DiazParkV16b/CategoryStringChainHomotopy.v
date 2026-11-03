(** Actual free-generator natural-transformation prism on category strings. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarPaths BarFreeModule.
From DiazParkV16b Require Import ChainComplex CategoryStringChains CategoryStringChainsMaps
  CategoryBarPullbackPaths CategoryBarPullbackPrism AlternatingPrism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DiazParkBarPaths DPChainComplex
  DPCategoryBarPullback DPCategoryBarPrism DPAlternatingPrism.
Local Open Scope ring_scope.

Module DPCategoryStringChainHomotopy.
Section Prism.
Variable R : pzRingType.
Variables C D : category.
Variables f g : functor C D.
Variable alpha : nat_trans f g.
Local Notation P := (path_prism alpha).

Lemma first_face n s : @path_face D n 0 (P n 0 s) = path_map g n s.
Proof. exact: path_prism_first_face. Qed.
Lemma last_face n s : @path_face D n n.+1 (P n n s) = path_map f n s.
Proof. exact: path_prism_last_face. Qed.
Lemma middle_face n i s : (i < n)%N ->
  @path_face D n i.+1 (P n i s) = @path_face D n i.+1 (P n i.+1 s).
Proof. move=> /ltP hi; exact (@path_prism_middle_face C D f g alpha n i s hi). Qed.
Lemma left_face n i j s : (i <= n)%N -> (j <= i)%N ->
  @path_face D n.+1 j (P n.+1 i.+1 s) = P n i (@path_face C n j s).
Proof. move=> /leP hi /leP hj; exact (@path_prism_left_face C D f g alpha n i j s hi hj). Qed.
Lemma right_face n i j s : (i <= j)%N -> (j <= n)%N ->
  @path_face D n.+1 j.+2 (P n.+1 i s) = P n i (@path_face C n j.+1 s).
Proof. move=> /leP hi /leP hj; exact (@path_prism_right_face C D f g alpha n i j s hi hj). Qed.

Definition prism_chain_at n (a : category_string_term R C n) : category_string_term R D n.+1 :=
  \sum_(i < n.+1) (-1 : R) ^+ i *: free_map R (P n i) a.
Arguments prism_chain_at n a : clear implicits.

Lemma prism_chain_at_linear n : linear (prism_chain_at n).
Proof.
move=> r a b; rewrite /prism_chain_at scaler_sumr -big_split.
apply eq_bigr => i _; by rewrite linearP scalerDr !scalerA commr_sign.
Qed.
Arguments prism_chain_at_linear n : clear implicits.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _
  (prism_chain_at n) (prism_chain_at_linear n).

Lemma prism_chain_at_basis n (s : @path C n) :
  prism_chain_at n (free_basis R s) =
    \sum_(i < n.+1) (-1 : R) ^+ i *: free_basis R (P n i s).
Proof. apply eq_bigr => i _; by rewrite free_map_basis. Qed.

Lemma boundary_basis n (s : @path D n.+1) :
  @category_string_boundary R D n (free_basis R s) =
    \sum_(j < n.+2) (-1 : R) ^+ j *: free_basis R (@path_face D n j s).
Proof. apply eq_bigr => j _; by rewrite /category_string_face free_map_basis. Qed.

Lemma boundary_after_prism n (s : @path C n) :
  @category_string_boundary R D n (prism_chain_at n (free_basis R s)) =
    rectangle n.+1 n.+2 (fun i j => free_basis R (@path_face D n j (P n i s))).
Proof.
rewrite prism_chain_at_basis linear_sum /rectangle.
apply eq_bigr => i _; rewrite linearZ.
change ((-1 : R)^+i *: @category_string_boundary R D n (free_basis R (P n i s)) =
  \sum_(j < n.+2) signed (i+j) (free_basis R (@path_face D n j (P n i s)))).
rewrite boundary_basis scaler_sumr.
apply eq_bigr => j _; by rewrite /signed scalerA -exprD.
Qed.

Lemma prism_after_boundary n (s : @path C n.+1) :
  prism_chain_at n (@category_string_boundary R C n (free_basis R s)) =
    rectangle n.+1 n.+2 (fun i j => free_basis R (P n i (@path_face C n j s))).
Proof.
rewrite /prism_chain_at /category_string_boundary /rectangle.
apply eq_bigr => i _; rewrite linear_sum scaler_sumr.
apply eq_bigr => j _.
by rewrite linearZ /category_string_face !free_map_basis /signed scalerA -exprD.
Qed.

Lemma prism_chain_zero_basis (s : @path C 0) :
  @category_string_boundary R D 0 (prism_chain_at 0 (free_basis R s)) =
    category_string_map_at R g 0 (free_basis R s) - category_string_map_at R f 0 (free_basis R s).
Proof.
rewrite boundary_after_prism /rectangle big_ord1 big_ord_recl big_ord1.
rewrite /signed add0n expr0 expr1 scale1r scaleN1r /category_string_map_at !free_map_basis.
by rewrite first_face last_face.
Qed.

Lemma prism_chain_succ_basis n (s : @path C n.+1) :
  @category_string_boundary R D n.+1 (prism_chain_at n.+1 (free_basis R s)) +
    prism_chain_at n (@category_string_boundary R C n (free_basis R s)) =
    category_string_map_at R g n.+1 (free_basis R s) - category_string_map_at R f n.+1 (free_basis R s).
Proof.
rewrite boundary_after_prism prism_after_boundary /category_string_map_at !free_map_basis.
rewrite -(@first_face n.+1 s) -(@last_face n.+1 s).
apply alternating_prism.
- move=> i j hi hj; case: i hi hj => [|i] hi hj; first by rewrite ltn0 in hj.
  by rewrite left_face.
- move=> i j hi hj hij; case: j hj hij => [|[|j]] hj hij.
  + by rewrite ltn0 in hij.
  + by rewrite ltnS leqn0 in hij.
  + by rewrite right_face.
- move=> i hi; by rewrite middle_face.
Qed.

Lemma prism_chain_zero (a : category_string_term R C 0) :
  @category_string_boundary R D 0 (prism_chain_at 0 a) =
    category_string_map_at R g 0 a - category_string_map_at R f 0 a.
Proof.
apply (free_lift_ext
  (g := (chain_d (category_string_chain R D) 0 \o
    (prism_chain_at 0 : {linear category_string_term R C 0 -> category_string_term R D 1}) : {linear _ -> _}))
  (h := (category_string_map_at R g 0 \- category_string_map_at R f 0 : {linear _ -> _}))).
exact: prism_chain_zero_basis.
Qed.

Lemma prism_chain_succ n (a : category_string_term R C n.+1) :
  @category_string_boundary R D n.+1 (prism_chain_at n.+1 a) +
    prism_chain_at n (@category_string_boundary R C n a) =
    category_string_map_at R g n.+1 a - category_string_map_at R f n.+1 a.
Proof.
apply (free_lift_ext
  (g := ((chain_d (category_string_chain R D) n.+1 \o
      (prism_chain_at n.+1 : {linear category_string_term R C n.+1 -> category_string_term R D n.+2})) \+
    ((prism_chain_at n : {linear category_string_term R C n -> category_string_term R D n.+1}) \o
      chain_d (category_string_chain R C) n) : {linear _ -> _}))
  (h := (category_string_map_at R g n.+1 \- category_string_map_at R f n.+1 : {linear _ -> _}))).
exact: prism_chain_succ_basis.
Qed.

Definition category_string_nat_trans_homotopy :
    chain_homotopy (category_string_chain_map R g) (category_string_chain_map R f) :=
  @ChainHomotopy R (category_string_chain R C) (category_string_chain R D) (category_string_chain_map R g) (category_string_chain_map R f)
    (fun n => (prism_chain_at n : {linear category_string_term R C n -> category_string_term R D n.+1}))
    prism_chain_zero prism_chain_succ.

End Prism.
End DPCategoryStringChainHomotopy.

Print Assumptions DPCategoryStringChainHomotopy.category_string_nat_trans_homotopy.
