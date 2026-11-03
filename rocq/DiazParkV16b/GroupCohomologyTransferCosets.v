(** Finite right-coset sums of actual left-invariant functions. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.

Module DPGroupCohomologyTransferCosets.
Section Cosets.
Variable G : finGroupType.
Variable V : zmodType.

Definition left_invariant (P : {group G}) (F : G -> V) : Prop :=
  forall p, p \in P -> forall x, F (p * x) = F x.

Definition coset_sum (P Q : {group G}) (F : G -> V) : V :=
  \sum_(C in rcosets P Q) F (repr C).

Lemma invariant_repr (P : {group G}) (F : G -> V)
    (hF : left_invariant P F) x : F (repr (P :* x)) = F x.
Proof. case: (repr_rcosetP P x) => p hp; exact: hF. Qed.

Lemma invariant_repr_mul (P : {group G}) (F : G -> V)
    (hF : left_invariant P F) x a : F (repr (P :* x) * a) = F (x * a).
Proof. case: (repr_rcosetP P x) => p hp; rewrite -mulgA; exact: hF. Qed.

Lemma invariant_rcoset_eq (P : {group G}) (F : G -> V)
    (hF : left_invariant P F) x y : P :* x = P :* y -> F x = F y.
Proof.
move=> h; by rewrite -(invariant_repr hF x) h invariant_repr.
Qed.

Lemma coset_sum_representatives (P Q : {group G}) (F : G -> V)
    (hF : left_invariant P F) (s : {set G} -> G)
    (hs : forall C, C \in rcosets P Q -> s C \in C) :
  coset_sum P Q F = \sum_(C in rcosets P Q) F (s C).
Proof.
apply: eq_bigr => C hC.
have hmem := hs C hC.
case/rcosetsP: hC => x hx e; subst C.
rewrite invariant_repr //.
case/rcosetP: hmem => p hp ->; symmetry; exact: hF.
Qed.

Lemma right_translate_rcosets (P Q : {group G}) a : a \in Q ->
  forall C : {set G}, (C :* a \in rcosets P Q) = (C \in rcosets P Q).
Proof.
move=> ha C.
rewrite -rcosetE.
exact (acts_act (actsRs_rcosets P Q) ha C).
Qed.

Lemma coset_sum_right_invariant (P Q : {group G}) (F : G -> V)
    (hF : left_invariant P F) a : a \in Q ->
  coset_sum P Q (fun x => F (x * a)) = coset_sum P Q F.
Proof.
move=> ha; rewrite /coset_sum [RHS](reindex_inj (@rcoset_inj G a)).
apply: eq_big.
- move=> C; symmetry; exact: right_translate_rcosets ha C.
- move=> C hC; case/rcosetsP: hC => x hx ->.
  by rewrite -rcosetM invariant_repr_mul // invariant_repr.
Qed.

Lemma coset_sum_self (P : {group G}) (F : G -> V) :
  coset_sum P P F = F 1.
Proof. by rewrite /coset_sum rcosets_id big_set1 repr_group. Qed.

End Cosets.
End DPGroupCohomologyTransferCosets.
