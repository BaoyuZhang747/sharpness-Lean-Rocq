From HB Require Import structures.
From Stdlib Require Import Lia.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules HomologicalComplex BarPaths BarComplex.
From DiazParkV16b Require Import CategoryBarPullbackPaths CategoryBarPullbackConstant
  CategoryBarPullbackPrism AlternatingPrism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkBarPaths DiazParkBarComplex
  DPCategoryBarPullback DPCategoryBarConstant DPCategoryBarPrism DPAlternatingPrism.
Local Open Scope ring_scope.

Module DPCategoryBarHomotopy.

Section Evaluation.
Variable R : pzRingType.
Variable C : category.
Variable A : lmodType R.

Definition constant_bar_evaluate n (a : cochain_term (constant_bar R C A) n)
    (p : @path C n) : A :=
  match p with existT x q => a x q end.

Lemma constant_bar_evaluate_coface n i
    (a : cochain_term (constant_bar R C A) n) (p : @path C n.+1) :
  constant_bar_evaluate (bar_coface (D := constant_coefficient R C A) i a) p =
  constant_bar_evaluate a (@path_face C n i p).
Proof. case: p => x q; case: i => [|i]; last reflexivity.
case: q => y [f r]; reflexivity. Qed.

End Evaluation.

Section Homotopy.
Variable R : pzRingType.
Variable A : lmodType R.
Variables C D : category.
Variables F G : functor C D.
Variable alpha : nat_trans F G.

Definition prism_cochain_at n i
    (a : cochain_term (constant_bar R D A) n.+1) :
    cochain_term (constant_bar R C A) n :=
  fun x p => a (fobj F x) (path_prism_from alpha n i x p).

Arguments prism_cochain_at n i a : clear implicits.

Lemma prism_cochain_at_linear n i : linear (prism_cochain_at n i).
Proof.
move=> r a b; apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p; reflexivity.
Qed.

Arguments prism_cochain_at_linear n i : clear implicits.

HB.instance Definition _ n i :=
  GRing.isLinear.Build R _ _ _ (prism_cochain_at n i) (prism_cochain_at_linear n i).

Lemma prism_cochain_first_face n (a : cochain_term (constant_bar R D A) n) :
  prism_cochain_at n 0 (bar_coface (D := constant_coefficient R D A) 0 a) =
  cochain_map_at (constant_bar_pullback A G) n a.
Proof.
apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
change (constant_bar_evaluate
  (bar_coface (D := constant_coefficient R D A) 0 a)
  (path_prism alpha n 0 (existT _ x p)) =
  constant_bar_evaluate a (path_map G n (existT _ x p))).
by rewrite constant_bar_evaluate_coface path_prism_first_face.
Qed.

Lemma prism_cochain_last_face n (a : cochain_term (constant_bar R D A) n) :
  prism_cochain_at n n (bar_coface (D := constant_coefficient R D A) n.+1 a) =
  cochain_map_at (constant_bar_pullback A F) n a.
Proof.
apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
change (constant_bar_evaluate
  (bar_coface (D := constant_coefficient R D A) n.+1 a)
  (path_prism alpha n n (existT _ x p)) =
  constant_bar_evaluate a (path_map F n (existT _ x p))).
by rewrite constant_bar_evaluate_coface path_prism_last_face.
Qed.

Lemma prism_cochain_middle_face n i (a : cochain_term (constant_bar R D A) n) :
  (i < n)%N ->
  prism_cochain_at n i (bar_coface (D := constant_coefficient R D A) i.+1 a) =
  prism_cochain_at n i.+1 (bar_coface (D := constant_coefficient R D A) i.+1 a).
Proof.
move=> /ltP hi; apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
change (constant_bar_evaluate
  (bar_coface (D := constant_coefficient R D A) i.+1 a)
  (path_prism alpha n i (existT _ x p)) =
  constant_bar_evaluate (bar_coface (D := constant_coefficient R D A) i.+1 a)
  (path_prism alpha n i.+1 (existT _ x p))).
by rewrite !constant_bar_evaluate_coface path_prism_middle_face.
Qed.

Lemma prism_cochain_left_face n i j (a : cochain_term (constant_bar R D A) n.+1) :
  (i <= n)%N -> (j <= i)%N ->
  prism_cochain_at n.+1 i.+1 (bar_coface (D := constant_coefficient R D A) j a) =
  bar_coface (D := constant_coefficient R C A) j (prism_cochain_at n i a).
Proof.
move=> /leP hi /leP hj; apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
change (constant_bar_evaluate
  (bar_coface (D := constant_coefficient R D A) j a)
  (path_prism alpha n.+1 i.+1 (existT _ x p)) =
  constant_bar_evaluate (bar_coface (D := constant_coefficient R C A) j
    (prism_cochain_at n i a)) (existT _ x p)).
rewrite !constant_bar_evaluate_coface path_prism_left_face //.
by case: (@path_face C n j (existT _ x p)).
Qed.

Lemma prism_cochain_right_face n i j (a : cochain_term (constant_bar R D A) n.+1) :
  (i <= j)%N -> (j <= n)%N ->
  prism_cochain_at n.+1 i (bar_coface (D := constant_coefficient R D A) j.+2 a) =
  bar_coface (D := constant_coefficient R C A) j.+1 (prism_cochain_at n i a).
Proof.
move=> /leP hi /leP hj; apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
change (constant_bar_evaluate
  (bar_coface (D := constant_coefficient R D A) j.+2 a)
  (path_prism alpha n.+1 i (existT _ x p)) =
  constant_bar_evaluate (bar_coface (D := constant_coefficient R C A) j.+1
    (prism_cochain_at n i a)) (existT _ x p)).
rewrite !constant_bar_evaluate_coface path_prism_right_face //.
Qed.

Definition constant_prism_homotopy_at n
    (a : cochain_term (constant_bar R D A) n.+1) :
    cochain_term (constant_bar R C A) n :=
  \sum_(i < n.+1) (-1 : R) ^+ i *: prism_cochain_at n i a.

Arguments constant_prism_homotopy_at n a : clear implicits.

Lemma constant_prism_homotopy_at_linear n : linear (constant_prism_homotopy_at n).
Proof.
move=> r a b; rewrite /constant_prism_homotopy_at scaler_sumr -big_split.
apply eq_bigr => i _.
by rewrite linearP scalerDr !scalerA commr_sign.
Qed.

Arguments constant_prism_homotopy_at_linear n : clear implicits.

HB.instance Definition _ n := GRing.isLinear.Build R _ _ _
  (constant_prism_homotopy_at n) (constant_prism_homotopy_at_linear n).

Lemma constant_prism_homotopy_zero (a : cochain_term (constant_bar R D A) 0) :
  cochain_map_at (constant_bar_pullback A G) 0 a -
    cochain_map_at (constant_bar_pullback A F) 0 a =
  constant_prism_homotopy_at 0 (cochain_d (constant_bar R D A) 0 a).
Proof.
change (cochain_map_at (constant_bar_pullback A G) 0 a -
  cochain_map_at (constant_bar_pullback A F) 0 a =
  constant_prism_homotopy_at 0 (bar_d (constant_coefficient R D A) 0 a)).
rewrite /constant_prism_homotopy_at big_ord1 expr0 scale1r.
rewrite bar_d_formula big_ord_recl big_ord1 expr0 expr1 scale1r scaleN1r.
rewrite linearB.
change (cochain_map_at (constant_bar_pullback A G) 0 a -
  cochain_map_at (constant_bar_pullback A F) 0 a =
  prism_cochain_at 0 0 (bar_coface (D := constant_coefficient R D A) 0 a) -
  prism_cochain_at 0 0 (bar_coface (D := constant_coefficient R D A) 1 a)).
by rewrite prism_cochain_first_face prism_cochain_last_face.
Qed.

Lemma constant_prism_homotopy_after_d n (a : cochain_term (constant_bar R D A) n) :
  constant_prism_homotopy_at n (bar_d (constant_coefficient R D A) n a) =
  rectangle n.+1 n.+2 (fun i j =>
    prism_cochain_at n i (bar_coface (D := constant_coefficient R D A) j a)).
Proof.
rewrite /constant_prism_homotopy_at /rectangle bar_d_formula.
apply eq_bigr => i _; rewrite linear_sum scaler_sumr.
apply eq_bigr => j _.
by rewrite linearZ /signed scalerA -exprD.
Qed.

Lemma constant_prism_homotopy_before_d n (a : cochain_term (constant_bar R D A) n.+1) :
  bar_d (constant_coefficient R C A) n (constant_prism_homotopy_at n a) =
  rectangle n.+1 n.+2 (fun i j =>
    bar_coface (D := constant_coefficient R C A) j (prism_cochain_at n i a)).
Proof.
rewrite bar_d_formula /constant_prism_homotopy_at /rectangle exchange_big.
apply eq_bigr => j _; rewrite linear_sum scaler_sumr.
apply eq_bigr => i _.
by rewrite linearZ /signed scalerA -exprD addnC.
Qed.

Lemma constant_prism_homotopy_succ n (a : cochain_term (constant_bar R D A) n.+1) :
  cochain_map_at (constant_bar_pullback A G) n.+1 a -
    cochain_map_at (constant_bar_pullback A F) n.+1 a =
  cochain_d (constant_bar R C A) n (constant_prism_homotopy_at n a) +
    constant_prism_homotopy_at n.+1 (cochain_d (constant_bar R D A) n.+1 a).
Proof.
have h := @alternating_prism R (cochain_term (constant_bar R C A) n.+1) n.+1
  (fun i j => prism_cochain_at n.+1 i
    (bar_coface (D := constant_coefficient R D A) j a))
  (fun i j => bar_coface (D := constant_coefficient R C A) j
    (prism_cochain_at n i a)).
have heq : rectangle n.+2 n.+3 (fun i j => prism_cochain_at n.+1 i
    (bar_coface (D := constant_coefficient R D A) j a)) +
  rectangle n.+1 n.+2 (fun i j => bar_coface (D := constant_coefficient R C A) j
    (prism_cochain_at n i a)) =
  cochain_map_at (constant_bar_pullback A G) n.+1 a -
    cochain_map_at (constant_bar_pullback A F) n.+1 a.
  rewrite -prism_cochain_first_face -prism_cochain_last_face.
  apply h.
  - move=> i j hi hj; case: i hi hj => [|i] hi hj; first by rewrite ltn0 in hj.
    apply prism_cochain_left_face; assumption.
  - move=> i j hi hj hij; case: j hj hij => [|[|j]] hj hij.
    + by rewrite ltn0 in hij.
    + by rewrite ltnS leqn0 in hij.
    + apply prism_cochain_right_face; assumption.
  - move=> i hi; exact: prism_cochain_middle_face hi.
change (cochain_map_at (constant_bar_pullback A G) n.+1 a -
    cochain_map_at (constant_bar_pullback A F) n.+1 a =
  bar_d (constant_coefficient R C A) n (constant_prism_homotopy_at n a) +
    constant_prism_homotopy_at n.+1 (bar_d (constant_coefficient R D A) n.+1 a)).
rewrite constant_prism_homotopy_before_d constant_prism_homotopy_after_d.
rewrite [RHS]addrC.
exact: esym heq.
Qed.

Definition constant_bar_nat_trans_homotopy :
    cochain_homotopy (constant_bar_pullback A G) (constant_bar_pullback A F) :=
  @CochainHomotopy R (constant_bar R D A) (constant_bar R C A)
    (constant_bar_pullback A G) (constant_bar_pullback A F)
    (fun n => (constant_prism_homotopy_at n :
      {linear cochain_term (constant_bar R D A) n.+1 ->
        cochain_term (constant_bar R C A) n}))
    constant_prism_homotopy_zero constant_prism_homotopy_succ.

End Homotopy.
Arguments constant_bar_nat_trans_homotopy {R} A {C D F G} alpha.
End DPCategoryBarHomotopy.
