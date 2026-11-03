(** Torsion-safe cancellation and permutation signs for actual subdivision. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory GroupScope.
Local Open Scope ring_scope.

Module DPSubdivisionPermutationSigns.
Section Cancellation.
Variable V : zmodType.
Variable I : finType.
Variable t : I -> I.
Hypothesis ht : involutive t.
Variable b : I -> bool.
Hypothesis hb : forall x, b (t x) = ~~ b x.
Variable F : I -> V.
Hypothesis hF : forall x, F (t x) = - F x.

Theorem involution_sum_zero : \sum_x F x = 0.
Proof.
rewrite (bigID b) /=.
have e : \sum_(x | ~~ b x) F x = - \sum_(x | b x) F x.
  rewrite (reindex_inj (can_inj ht)).
  under eq_bigl do rewrite hb negbK.
  under eq_bigr do rewrite hF.
  exact: sumrN.
by rewrite e addrN.
Qed.
End Cancellation.

Section PermutationSigns.
Variable R : pzRingType.
Variable T : finType.
Definition permutation_sign (p : {perm T}) : R := (-1) ^+ (odd_perm p).

Lemma permutation_sign_mul (p q : {perm T}) :
  permutation_sign (p * q)%g = permutation_sign p * permutation_sign q.
Proof. by rewrite /permutation_sign odd_permM signr_addb. Qed.

Lemma permutation_sign_transpose (x y : T) (h : x != y) (p : {perm T}) :
  permutation_sign (tperm x y * p)%g = - permutation_sign p.
Proof. by rewrite /permutation_sign odd_mul_tperm h addTb signrN. Qed.

Theorem transpose_invariant_sum_zero (V : lmodType R) (x y : T)
    (h : x != y) (F : {perm T} -> V)
    (hF : forall p, F (tperm x y * p)%g = F p) :
  \sum_p permutation_sign p *: F p = 0.
Proof.
refine (@involution_sum_zero V [the finType of {perm T}]
  (fun p => (tperm x y * p)%g) (tpermKg x y) (fun p => odd_perm p) _
  (fun p => permutation_sign p *: F p) _).
- by move=> p; rewrite odd_mul_tperm h addTb.
- by move=> p; rewrite permutation_sign_transpose // hF scaleNr.
Qed.
End PermutationSigns.
End DPSubdivisionPermutationSigns.
