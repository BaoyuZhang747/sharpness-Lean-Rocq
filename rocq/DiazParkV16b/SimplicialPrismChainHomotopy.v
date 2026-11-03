(** Actual free-generator prism on simplicial chains. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplicialSet SimplicialChains
  SimplicialChainsMaps AlternatingPrism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPSimplicialSet
  DPSimplicialChains DPSimplicialChainMaps DPAlternatingPrism.
Local Open Scope ring_scope.

Module DPSimplicialPrismChainHomotopy.
Section Prism.
Variable R : pzRingType.
Variables X Y : simplicial_set.
Variables f g : simplicial_map X Y.
Variable P : forall n, nat -> simplex X n -> simplex Y n.+1.
Arguments P n _ _ : clear implicits.
Hypothesis first_face : forall n s,
  @indexed_face Y n 0 (P n 0 s) = component g n s.
Hypothesis last_face : forall n s,
  @indexed_face Y n n.+1 (P n n s) = component f n s.
Hypothesis middle_face : forall n i s, (i < n)%N ->
  @indexed_face Y n i.+1 (P n i s) = @indexed_face Y n i.+1 (P n i.+1 s).
Hypothesis left_face : forall n i j s, (i <= n)%N -> (j <= i)%N ->
  @indexed_face Y n.+1 j (P n.+1 i.+1 s) = P n i (@indexed_face X n j s).
Hypothesis right_face : forall n i j s, (i <= j)%N -> (j <= n)%N ->
  @indexed_face Y n.+1 j.+2 (P n.+1 i s) = P n i (@indexed_face X n j.+1 s).

Definition prism_chain_at n (a : term R X n) : term R Y n.+1 :=
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

Lemma prism_chain_at_basis n (s : simplex X n) :
  prism_chain_at n (free_basis R s) =
    \sum_(i < n.+1) (-1 : R) ^+ i *: free_basis R (P n i s).
Proof. apply eq_bigr => i _; by rewrite free_map_basis. Qed.

Lemma boundary_basis n (s : simplex Y n.+1) :
  @DPSimplicialChains.boundary R Y n (free_basis R s) =
    \sum_(j < n.+2) (-1 : R) ^+ j *: free_basis R (@indexed_face Y n j s).
Proof. apply eq_bigr => j _; by rewrite /face_map free_map_basis. Qed.

Lemma boundary_after_prism n (s : simplex X n) :
  @DPSimplicialChains.boundary R Y n (prism_chain_at n (free_basis R s)) =
    rectangle n.+1 n.+2 (fun i j => free_basis R (@indexed_face Y n j (P n i s))).
Proof.
rewrite prism_chain_at_basis linear_sum /rectangle.
apply eq_bigr => i _; rewrite linearZ.
change ((-1 : R)^+i *: @DPSimplicialChains.boundary R Y n (free_basis R (P n i s)) =
  \sum_(j < n.+2) signed (i+j) (free_basis R (@indexed_face Y n j (P n i s)))).
rewrite boundary_basis scaler_sumr.
apply eq_bigr => j _; by rewrite /signed scalerA -exprD.
Qed.

Lemma prism_after_boundary n (s : simplex X n.+1) :
  prism_chain_at n (@DPSimplicialChains.boundary R X n (free_basis R s)) =
    rectangle n.+1 n.+2 (fun i j => free_basis R (P n i (@indexed_face X n j s))).
Proof.
rewrite /prism_chain_at /DPSimplicialChains.boundary /rectangle.
apply eq_bigr => i _; rewrite linear_sum scaler_sumr.
apply eq_bigr => j _.
by rewrite linearZ /face_map !free_map_basis /signed scalerA -exprD.
Qed.

Lemma prism_chain_zero_basis (s : simplex X 0) :
  @DPSimplicialChains.boundary R Y 0 (prism_chain_at 0 (free_basis R s)) =
    map_at R g 0 (free_basis R s) - map_at R f 0 (free_basis R s).
Proof.
rewrite boundary_after_prism /rectangle big_ord1 big_ord_recl big_ord1.
rewrite /signed add0n expr0 expr1 scale1r scaleN1r !map_at_basis.
by rewrite first_face last_face.
Qed.

Lemma prism_chain_succ_basis n (s : simplex X n.+1) :
  @DPSimplicialChains.boundary R Y n.+1 (prism_chain_at n.+1 (free_basis R s)) +
    prism_chain_at n (@DPSimplicialChains.boundary R X n (free_basis R s)) =
    map_at R g n.+1 (free_basis R s) - map_at R f n.+1 (free_basis R s).
Proof.
rewrite boundary_after_prism prism_after_boundary !map_at_basis.
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

Lemma prism_chain_zero (a : term R X 0) :
  @DPSimplicialChains.boundary R Y 0 (prism_chain_at 0 a) =
    map_at R g 0 a - map_at R f 0 a.
Proof.
apply (free_lift_ext
  (g := (chain_d (chains R Y) 0 \o
    (prism_chain_at 0 : {linear term R X 0 -> term R Y 1}) : {linear _ -> _}))
  (h := (map_at R g 0 \- map_at R f 0 : {linear _ -> _}))).
exact: prism_chain_zero_basis.
Qed.

Lemma prism_chain_succ n (a : term R X n.+1) :
  @DPSimplicialChains.boundary R Y n.+1 (prism_chain_at n.+1 a) +
    prism_chain_at n (@DPSimplicialChains.boundary R X n a) =
    map_at R g n.+1 a - map_at R f n.+1 a.
Proof.
apply (free_lift_ext
  (g := ((chain_d (chains R Y) n.+1 \o
      (prism_chain_at n.+1 : {linear term R X n.+1 -> term R Y n.+2})) \+
    ((prism_chain_at n : {linear term R X n -> term R Y n.+1}) \o
      chain_d (chains R X) n) : {linear _ -> _}))
  (h := (map_at R g n.+1 \- map_at R f n.+1 : {linear _ -> _}))).
exact: prism_chain_succ_basis.
Qed.

Definition simplicial_prism_chain_homotopy :
    chain_homotopy (chain_map_of R g) (chain_map_of R f) :=
  @ChainHomotopy R (chains R X) (chains R Y) (chain_map_of R g) (chain_map_of R f)
    (fun n => (prism_chain_at n : {linear term R X n -> term R Y n.+1}))
    prism_chain_zero prism_chain_succ.

End Prism.
End DPSimplicialPrismChainHomotopy.
