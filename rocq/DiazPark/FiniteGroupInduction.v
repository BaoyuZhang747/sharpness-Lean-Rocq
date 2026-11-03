From mathcomp Require Import all_ssreflect all_fingroup.
From DiazPark Require Import InductionOrder.

(** Ordinary strong induction on the cardinality of actual finite groups.
    The induction hypothesis ranges over different finite carrier types, as
    required for subgroup quotients. These are induction rules, not a
    substituted assumption or an implementation of the sharpness theorem. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Theorem finite_group_type_order_induction (P : finGroupType -> Prop) :
  (forall G : finGroupType,
    (forall H : finGroupType, #|H| < #|G| -> P H) -> P G) ->
  forall G : finGroupType, P G.
Proof.
move=> step.
have by_card : forall n, forall G : finGroupType, #|G| = n -> P G.
  apply: ltn_ind => n IHn G cardG.
  apply: step => H ltHG.
  apply: (IHn #|H|); last by [].
  by rewrite -cardG.
move=> G; exact: (by_card #|G| G erefl).
Qed.

Theorem finite_group_order_induction
    (P : forall gT : finGroupType, {group gT} -> Prop) :
  (forall (gT : finGroupType) (G : {group gT}),
    (forall (hT : finGroupType) (H : {group hT}),
      #|H| < #|G| -> P hT H) -> P gT G) ->
  forall (gT : finGroupType) (G : {group gT}), P gT G.
Proof.
move=> step.
have by_card : forall n, forall (gT : finGroupType) (G : {group gT}),
    #|G| = n -> P gT G.
  apply: ltn_ind => n IHn gT G cardG.
  apply: step => hT H ltHG.
  apply: (IHn #|H|); last by [].
  by rewrite -cardG.
move=> gT G.
exact: (by_card #|G| gT G erefl).
Qed.

Theorem finite_group_order_induction_from_trivial
    (P : forall gT : finGroupType, {group gT} -> Prop) :
  (forall (gT : finGroupType) (G : {group gT}), G :=: 1 -> P gT G) ->
  (forall (gT : finGroupType) (G : {group gT}), G :!=: 1 ->
    (forall (hT : finGroupType) (H : {group hT}),
      #|H| < #|G| -> P hT H) -> P gT G) ->
  forall (gT : finGroupType) (G : {group gT}), P gT G.
Proof.
move=> base step; apply: finite_group_order_induction => gT G IH.
case: (boolP (G :==: 1)) => hG.
- exact: base (eqP hG).
- exact: step hG IH.
Qed.
