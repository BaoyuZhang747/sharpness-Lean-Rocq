(** The actual Alexander--Whitney boundary formula on every simplex generator. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators SimplexCategoryIdentities
  SimplicialSet SimplicialSetOperators BisimplicialSet BisimplicialChains
  BisimplicialAlexanderWhitneyOrdinals BisimplicialAlexanderWhitneyFaces BisimplicialAlexanderWhitneySigns.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPSimplexCategory DPSimplexOperators DPSimplexIdentities
  DPSimplicialSet DPSimplicialOperators DPBisimplicialSet DPBisimplicialChains
  DPAlexanderWhitneyOrdinals DPAlexanderWhitneyFaces DPAlexanderWhitneySigns.
Local Open Scope ring_scope.

Module DPAlexanderWhitneyBoundary.
Section Boundary.
Variable R : pzRingType.
Variable X : bisimplicial_set.
Theorem aw_boundary p q n (h : Nat.add p q = n) (x : simplex (diagonal X) n.+1) :
  (\sum_(i < n.+2) (-1)^+i *: free_basis R
    (aw_simplex X p q n h (face (diagonal X) (inord i) x))) =
  (\sum_(i < p.+2) (-1)^+i *: free_basis R
    (horizontal_map X (coface (inord i)) q (aw_simplex X p.+1 q n.+1 (successor_left h) x))) +
  (-1)^+p *: (\sum_(j < q.+2) (-1)^+j *: free_basis R
    (face (fobj X p) (inord j) (aw_simplex X p q.+1 n.+1 (successor_right h) x))).
Proof.
apply (@alternating_split_degree R (bi_term R X p q) p q n h
  (fun i => free_basis R (aw_simplex X p q n h (face (diagonal X) (inord i) x)))
  (fun i => free_basis R (horizontal_map X (coface (inord i)) q
    (aw_simplex X p.+1 q n.+1 (successor_left h) x)))
  (fun j => free_basis R (face (fobj X p) (inord j)
    (aw_simplex X p q.+1 n.+1 (successor_right h) x)))).
- move=> i hi.
  have hin : (i < n.+2)%N := ltn_ord (early_index p q n h (Ordinal hi)).
  have ei : (inord i : 'I_n.+2) = early_index p q n h (Ordinal hi).
    apply val_inj; exact: inordK.
  have ep : (inord i : 'I_p.+2) = vertex_widen (Ordinal hi).
    apply val_inj; exact (@inordK p.+1 i (ltn_trans hi (ltnSn _))).
  rewrite ei ep; congr (free_basis R _); exact: aw_face_early.
- move=> j hj.
  have hin : ((p.+1+j)%N < n.+2)%N := ltn_ord (late_index p q n h (Ordinal hj)).
  have ej : (inord (p.+1+j) : 'I_n.+2) = late_index p q n h (Ordinal hj).
    apply val_inj; exact: inordK.
  have eq : (inord j.+1 : 'I_q.+2) = vertex_successor (Ordinal hj).
    apply val_inj; apply (@inordK q.+1 j.+1); by rewrite ltnS.
  rewrite ej eq; congr (free_basis R _); exact: aw_face_late.
- have ep : (inord p.+1 : 'I_p.+2) = ord_max by exact (@inord_val p.+1 ord_max).
  have eq : (inord 0 : 'I_q.+2) = ord0 by exact (@inord_val q.+1 ord0).
  rewrite ep eq; congr (free_basis R _); exact: aw_face_middle.
Qed.
End Boundary.
End DPAlexanderWhitneyBoundary.
