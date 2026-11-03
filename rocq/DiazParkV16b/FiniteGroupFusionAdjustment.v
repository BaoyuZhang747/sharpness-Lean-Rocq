(** A Sylow adjustment in a centralizer-normalizer product. *)
From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFiniteGroupFusionAdjustment.
Section Adjustment.
Variable G : finGroupType.
Variable p : nat.
Variables T Q A : {group G}.

Theorem sylow_central_adjust :
  p.-Sylow('N(Q)) 'N_T(Q) -> p.-group A ->
  A \subset 'C(Q) * 'N_T(Q) ->
  exists c : G, c \in 'C(Q) /\ A :^ c \subset 'N_T(Q).
Proof.
move=> sylN pA sA.
have nNC : 'N_T(Q) \subset 'N('C(Q)).
  exact: subset_trans (subsetIr T 'N(Q)) (normal_norm (cent_normal Q)).
pose J := ('C(Q) <*> 'N_T(Q))%G.
have eqJ : (J : {set G}) = 'C(Q) * 'N_T(Q) := norm_joinEr nNC.
have sJN : J \subset 'N(Q).
  by rewrite join_subG cent_sub (subsetIr T 'N(Q)).
have sNJ : 'N_T(Q) \subset J := joing_subr _ _.
have sylJ := pHall_subl sNJ sJN sylN.
have sAJ : A \subset J by rewrite eqJ.
have [g Jg sAg] := Sylow_Jsub sylJ sAJ pA.
rewrite eqJ in Jg; case/mulsgP: Jg=> c n Cc Nn eqg.
exists c; split=> //.
have NnN : n \in 'N('N_T(Q)) := subsetP (normG 'N_T(Q)%G) n Nn.
have Nni : n^-1 \in 'N('N_T(Q)) by rewrite groupV.
by rewrite eqg conjsgM sub_conjg (normP Nni) in sAg.
Qed.

End Adjustment.
End DPFiniteGroupFusionAdjustment.

Print Assumptions DPFiniteGroupFusionAdjustment.sylow_central_adjust.
