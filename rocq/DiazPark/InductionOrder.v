From mathcomp Require Import all_ssreflect all_fingroup center pgroup.

(** Group-theoretic facts used by the sharpness induction. Normality is
    explicit wherever an ordinary subgroup quotient is intended: MathComp's
    quotient operation is otherwise totalized through the normalizer.
    No fusion saturation or sharpness theorem is assumed here. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Section OrderDecrease.
Variable gT : finGroupType.

Lemma abelian_subgroup_central_in_centralizer (S E : {group gT}) :
  E \subset S -> abelian E -> E \subset 'Z('C_S(E)).
Proof.
move=> eS abE; rewrite /center subsetI.
apply/andP; split.
- apply/subsetIP; split; [exact: eS | exact: abE].
- by rewrite centsC subsetIr.
Qed.

Lemma abelian_subgroup_normal_in_centralizer (S E : {group gT}) :
  E \subset S -> abelian E -> E <| 'C_S(E).
Proof.
move=> eS abE.
exact: sub_center_normal (abelian_subgroup_central_in_centralizer eS abE).
Qed.

Lemma centralizer_quotient_card (S E : {group gT}) :
  E \subset S -> abelian E ->
  #|'C_S(E) / E| = #|'C_S(E)| %/ #|E|.
Proof.
move=> eS abE; apply: esym.
exact: divg_normal (abelian_subgroup_normal_in_centralizer eS abE).
Qed.

Lemma quotient_order_lt_ambient (S T E : {group gT}) :
  E :!=: 1 -> E <| T -> T \subset S -> #|T / E| < #|S|.
Proof.
move=> ntE nET tS.
exact: leq_trans (ltn_quotient ntE (normal_sub nET)) (subset_leq_card tS).
Qed.

Lemma centralizer_quotient_order_lt (S E : {group gT}) :
  E :!=: 1 -> E \subset S -> abelian E -> #|'C_S(E) / E| < #|S|.
Proof.
move=> ntE eS abE.
have nEC := abelian_subgroup_normal_in_centralizer eS abE.
exact: quotient_order_lt_ambient ntE nEC (subsetIl S 'C(E)).
Qed.

Lemma centralizer_quotient_order_bounds (S E : {group gT}) :
  E :!=: 1 -> E \subset S -> abelian E ->
  #|'C_S(E) / E| < #|'C_S(E)| /\ #|'C_S(E)| <= #|S|.
Proof.
move=> ntE eS abE; split.
- exact: ltn_quotient ntE
    (normal_sub (abelian_subgroup_normal_in_centralizer eS abE)).
- exact: subset_leq_card (subsetIl S 'C(E)).
Qed.

Lemma centralizer_quotient_pgroup (pi : nat_pred) (S E : {group gT}) :
  E \subset S -> abelian E -> pi.-group S -> pi.-group ('C_S(E) / E).
Proof.
move=> eS abE piS; apply: quotient_pgroup.
exact: pgroupS (subsetIl S 'C(E)) piS.
Qed.

Lemma subgroup_carrier_card (G : {group gT}) :
  #|{: [subg G]}| = #|G|.
Proof. by rewrite card_sub. Qed.

Lemma centralizer_quotient_carrier_order_lt (S E : {group gT}) :
  E :!=: 1 -> E \subset S -> abelian E ->
  #|{: [subg ('C_S(E) / E)%G]}| < #|S|.
Proof.
rewrite card_sub.
exact: centralizer_quotient_order_lt.
Qed.

Lemma subgroup_of_card_one (S P : {group gT}) :
  #|S| = 1%N -> P \subset S -> P :=: 1.
Proof.
move=> cardS; rewrite (card1_trivg cardS) subG1.
exact: eqP.
Qed.

Lemma no_nontrivial_subgroup_of_card_one (S E : {group gT}) :
  #|S| = 1%N -> E \subset S -> E :!=: 1 -> False.
Proof.
move=> cardS eS.
by rewrite (subgroup_of_card_one cardS eS) eqxx.
Qed.

Lemma card_one_subgroups_selfcentralizing (S P : {group gT}) :
  #|S| = 1%N -> P \subset S -> 'C_S(P) = P.
Proof.
move=> cardS pS.
by rewrite (subgroup_of_card_one cardS pS) (card1_trivg cardS)
  cent1T setIT.
Qed.

End OrderDecrease.
