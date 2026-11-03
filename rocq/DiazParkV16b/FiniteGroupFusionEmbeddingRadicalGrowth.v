(** An elementary finite p-group normalizer argument, with actual subgroups. *)
From mathcomp Require Import all_boot all_fingroup pgroup nilpotent sylow.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFiniteGroupFusionEmbeddingRadicalGrowth.
Section Growth.
Variable N : finGroupType.
Variable p : nat.
Hypothesis pN : p.-group [set: N].
Variables O P : {group N}.
Hypothesis nO : O <| [set: N].

Theorem normal_subgroup_contained_of_normalizer_inter :
  'N(P) :&: O \subset P -> O \subset P.
Proof.
move=> h; apply/negPn/negP=> notOP.
have nPO : P \subset 'N(O) := subset_trans (subsetT P) (normal_norm nO).
have ne : P != (P <*> O)%G.
  apply/eqP=> he; have hs := joing_subr P O.
  have he' : (P : {set N}) = P <*> O := congr1 val he.
  rewrite -he' in hs; by rewrite hs in notOP.
have pr : P \proper (P <*> O)%G by rewrite properEneq ne joing_subl.
have grow := nilpotent_proper_norm
  (pgroup_nil (pgroupS (subsetT (P <*> O)%G) pN)) pr.
have small : 'N_(P <*> O)(P) \subset P.
  apply/subsetP=> x /setIP[hx nx].
  rewrite (norm_joinEl nPO) in hx.
  have /imset2P[a b ha hb ex] := hx.
  have nb : b \in 'N(P).
    have na : a^-1 \in 'N(P) by rewrite groupV; exact: subsetP (normG P) _ ha.
    have hh := groupM na nx.
    by rewrite ex mulgA mulVg mul1g in hh.
  rewrite ex; apply: groupM ha _.
  have hnb : b \in 'N(P) :&: O by apply/setIP; split.
  exact: subsetP h _ hnb.
have hh := proper_card grow.
have hh' := subset_leq_card small.
by move: hh; rewrite ltnNge hh'.
Qed.
End Growth.
End DPFiniteGroupFusionEmbeddingRadicalGrowth.
