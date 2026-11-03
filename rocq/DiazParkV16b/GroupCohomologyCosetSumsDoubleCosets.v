(** Actual double cosets: Q-orbits on the right cosets P\T.  Their
    stabilizers are the literal intersections Q intersect P^x. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazParkV16b Require Import GroupCohomologyTransferCosets
  GroupCohomologyCosetSumsTowerCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomologyTransferCosets DPGroupCohomologyCosetSums.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.

Module DPGroupCohomologyCosetSumsDoubleCosets.
Section DoubleCosets.
Variable G : finGroupType.
Variables P Q T : {group G}.
Hypotheses (hPT : P \subset T) (hQT : Q \subset T).

Definition double_cosets : {set {set {set G}}} :=
  orbit 'Rs Q @: rcosets P T.

Lemma right_cosets_action : [acts Q, on rcosets P T | 'Rs].
Proof.
apply/actsP=> a Qa C.
exact (acts_act (actsRs_rcosets P T) (subsetP hQT _ Qa) C).
Qed.

Theorem double_cosets_partition : partition double_cosets (rcosets P T).
Proof. exact: orbit_partition right_cosets_action. Qed.

Definition chosen_coset (D : {set {set G}}) : {set G} :=
  odflt (P : {set G}) [pick C in D].

Lemma chosen_coset_mem D : D \in double_cosets -> chosen_coset D \in D.
Proof.
move=> hD; rewrite /chosen_coset; case: pickP=> [C CD|hnone] //.
have /imsetP[C hC he] := hD; subst D.
have := hnone C; by rewrite orbit_refl.
Qed.

Lemma chosen_coset_rcoset D : D \in double_cosets -> chosen_coset D \in rcosets P T.
Proof.
move=> hD; have hc := chosen_coset_mem hD.
have /imsetP[C hC he] := hD.
have hsub : D \subset rcosets P T by rewrite he (acts_sub_orbit C right_cosets_action).
exact: subsetP hsub _ hc.
Qed.

Definition double_coset_repr (D : {set {set G}}) : G := repr (chosen_coset D).

Lemma chosen_coset_repr D (hD : D \in double_cosets) :
  P :* double_coset_repr D = chosen_coset D.
Proof.
have /rcosetsP[x Tx hx] := chosen_coset_rcoset hD.
by rewrite /double_coset_repr hx rcoset_repr.
Qed.

Lemma double_coset_repr_mem D (hD : D \in double_cosets) : double_coset_repr D \in T.
Proof.
exact (@coset_representative_mem G P T hPT
  (exist (fun C : {set G} => is_true (C \in rcosets P T))
    (chosen_coset D) (chosen_coset_rcoset hD))).
Qed.

Lemma double_coset_orbit D (hD : D \in double_cosets) :
  orbit 'Rs Q (P :* double_coset_repr D) = D.
Proof.
rewrite chosen_coset_repr //.
have hc := chosen_coset_mem hD; have /imsetP[C hC he] := hD.
rewrite he in hc |- *.
exact (elimT (@orbit_eqP G [the finType of {set G}] 'Rs Q _ C) hc).
Qed.

Lemma double_coset_stabilizer x :
  'C_Q[P :* x | 'Rs] = Q :&: (P :^ x).
Proof.
rewrite -rcosetE.
change (Q :&: 'C['Rs (P : {set G}) x | 'Rs] = Q :&: (P :^ x)).
by rewrite astab1_act astab1Rs.
Qed.

Definition double_coset_carrier (D : {set {set G}}) : {set G} :=
  \bigcup_(C in D) C.

Lemma orbit_carrier x :
  double_coset_carrier (orbit 'Rs Q (P :* x)) = (P :* x) * Q.
Proof.
apply/setP=> y; apply/bigcupP/mulsgP.
- move=> [C /orbitP[q Qq hq] hy].
  rewrite -hq in hy; change (is_true (y \in rcoset (P :* x) q)) in hy.
  rewrite rcosetE in hy; case/rcosetP: hy=> z hz hy.
  exists z q=> //.
- move=> [z q hz hq ->].
  exists ((P :* x) :* q).
  + apply/orbitP; exists q=> //; exact: rcosetE.
  + apply/rcosetP; exists z=> //.
Qed.

Theorem double_coset_carrier_formula D (hD : D \in double_cosets) :
  double_coset_carrier D = (P :* double_coset_repr D) * Q.
Proof. rewrite -{1}(double_coset_orbit hD); exact: orbit_carrier. Qed.

Section Sum.
Variable V : zmodType.
Variable F : G -> V.
Hypothesis hF : left_invariant P F.

Lemma translated_left_invariant x :
  left_invariant (Q :&: (P :^ x)) (fun q => F (x * q)).
Proof.
move=> a /setIP[_ ha] q.
rewrite mem_conjg in ha.
have he : x * (a * q) = (a ^ x^-1) * (x * q).
  by rewrite /conjg invgK !mulgA mulgKV.
rewrite he; exact: hF.
Qed.

Lemma orbit_coset_sum x :
  \sum_(C in orbit 'Rs Q (P :* x)) F (repr C) =
    coset_sum (Q :&: (P :^ x)) Q (fun q => F (x * q)).
Proof.
rewrite (@orbit_stabilizer G [set: G] [the finType of {set G}] 'Rs Q (P :* x) (subsetT Q)) big_imset.
- rewrite /coset_sum double_coset_stabilizer.
  apply: eq_bigr=> U hU.
  change (F (repr (rcoset (P :* x) (repr U))) = F (x * repr U)).
  by rewrite rcosetE -rcosetM invariant_repr.
- exact: can_in_inj (@act_reprK G [set: G] [the finType of {set G}] 'Rs Q (P :* x) (subsetT Q)).
Qed.

Theorem coset_sum_double_coset :
  coset_sum P T F =
    \sum_(D in double_cosets)
      coset_sum (Q :&: (P :^ double_coset_repr D)) Q
        (fun q => F (double_coset_repr D * q)).
Proof.
rewrite /coset_sum (set_partition_big double_cosets double_cosets_partition).
apply: eq_bigr=> D hD.
rewrite -{1}(double_coset_orbit hD); exact: orbit_coset_sum.
Qed.

End Sum.
End DoubleCosets.
End DPGroupCohomologyCosetSumsDoubleCosets.

Print Assumptions DPGroupCohomologyCosetSumsDoubleCosets.coset_sum_double_coset.






