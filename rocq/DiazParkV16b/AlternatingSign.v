(** Finite alternating signs over arbitrary rings, including the zero ring. *)
From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Module DPAlternatingSign.
Section Signs.
Variable R : pzRingType.
Lemma sign_parity n : (-1 : R)^+n = if odd n then -1 else 1.
Proof.
elim: n => [|n IH]; first by rewrite expr0.
rewrite exprS IH oddS; case: (odd n) => /=; by rewrite ?mulN1r ?opprK ?mulr1.
Qed.
Lemma sum_sign n : \sum_(i < n) (-1 : R)^+i = if odd n then 1 else 0.
Proof.
elim: n => [|n IH]; first by rewrite big_ord0.
rewrite big_ord_recr IH sign_parity oddS.
case: (odd n) => /=; by rewrite ?addrN ?add0r.
Qed.
End Signs.
End DPAlternatingSign.
