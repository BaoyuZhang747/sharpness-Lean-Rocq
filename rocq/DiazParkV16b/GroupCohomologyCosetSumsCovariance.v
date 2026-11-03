(** Actual coset reindexing and trace covariance under an injective
    morphism on the ambient subgroup, with literal image subgroups. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazParkV16b Require Import GroupCohomologyTransferCosets
  GroupCohomologyCosetSumsTowerCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomologyTransferCosets DPGroupCohomologyCosetSums.
Local Open Scope ring_scope.
Local Open Scope group_scope.

Module DPGroupCohomologyCosetSumsCovariance.
Section Covariance.
Variables G G' : finGroupType.
Variables P Q : {group G}.
Hypothesis hPQ : P \subset Q.
Variable e : {morphism Q >-> G'}.
Hypothesis he : 'injm e.

Lemma coset_subset (C : coset_type P Q) : val C \subset Q.
Proof.
have /rcosetsP[x Qx hx] := valP C; rewrite hx -(rcoset_id Qx).
by rewrite rcosetS.
Qed.

Lemma coset_image_formula (C : coset_type P Q) :
  e @* val C = (e @* P) :* e (repr (val C)).
Proof.
rewrite -{1}(coset_representative C) morphimMl //.
by rewrite morphim_set1 // (coset_representative_mem hPQ C).
Qed.

Lemma coset_image_mem (C : coset_type P Q) :
  e @* val C \in rcosets (e @* P) (e @* Q).
Proof.
rewrite coset_image_formula; apply/rcosetsP; exists (e (repr (val C)))=> //.
apply: mem_morphim; exact: coset_representative_mem hPQ C.
Qed.

Definition coset_image (C : coset_type P Q) : coset_type (e @* P)%G (e @* Q)%G :=
  Sub (e @* val C) (coset_image_mem C).

Lemma coset_image_value (C : coset_type P Q) : val (coset_image C) = e @* val C.
Proof. reflexivity. Qed.

Theorem coset_image_injective : injective coset_image.
Proof.
move=> C D h; apply val_inj.
apply: (injm_morphim_inj he (coset_subset C) (coset_subset D)).
exact (congr1 (fun C : coset_type (e @* P)%G (e @* Q)%G => val C) h).
Qed.

Theorem coset_image_bijective : bijective coset_image.
Proof.
apply: inj_card_bij coset_image_injective _.
rewrite !card_sub.
change (#|(e @* Q)%G : (e @* P)%G| <= #|Q : P|)%N.
rewrite -(divgS (morphimS e hPQ)) -(divgS hPQ).
by rewrite !card_injm // ?subxx.
Qed.

Section Sum.
Variable V : zmodType.
Variable F : G' -> V.
Hypothesis hF : left_invariant (e @* P)%G F.

Theorem coset_sum_covariance :
  coset_sum P Q (fun x => F (e x)) = coset_sum (e @* P)%G (e @* Q)%G F.
Proof.
symmetry; rewrite /coset_sum [LHS]big_sub [RHS]big_sub.
rewrite (reindex coset_image); last exact: onW_bij coset_image_bijective.
apply: eq_bigr=> C _; rewrite coset_image_value coset_image_formula.
exact (invariant_repr hF _).
Qed.

Theorem coset_sum_covariance_named (P' Q' : {group G'})
    (hP' : (e @* P)%G = P') (hQ' : (e @* Q)%G = Q') :
  coset_sum P Q (fun x => F (e x)) = coset_sum P' Q' F.
Proof. by rewrite -hP' -hQ'; exact: coset_sum_covariance. Qed.

End Sum.
End Covariance.
End DPGroupCohomologyCosetSumsCovariance.

Print Assumptions DPGroupCohomologyCosetSumsCovariance.coset_sum_covariance.
