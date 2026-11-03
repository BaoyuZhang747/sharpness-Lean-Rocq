From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionSystems FusionMackeyShape FusionQuotientMaps FusionQuotientConstruction.
Import DPFusionMackey DPFusionQuotientConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientDoubleCosets.
Section Correspondence.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.

Lemma preimage_apex (P Q : {group coset_of Z}) t :
  preimage (inclusion_apex P Q (coset Z t)) =
  inclusion_apex (preimage P) (preimage Q) t.
Proof.
apply: val_inj; rewrite /preimage /inclusion_apex /= morphpreI.
by rewrite -morphV ?(normZ_all cZ) // morphpreJ ?(normZ_all cZ).
Qed.

Lemma preimage_double_coset (P Q : {group coset_of Z}) t :
  coset Z @*^-1 (double_coset P Q (coset Z t)) =
  double_coset (preimage P) (preimage Q) t.
Proof.
rewrite /double_coset !cosetpreM cosetpre_set1 ?(normZ_all cZ) //.
by rewrite mulgA (mulGSid (kernel_sub_preimage P)).
Qed.

Variables P Q T : {group coset_of Z}.

Lemma preimage_index_mem (i : double_coset_index P Q T) :
  coset Z @*^-1 val i \in double_coset (preimage P) (preimage Q) @: preimage T.
Proof.
pose q := double_coset_representative i.
apply/imsetP; exists (fingroup.repr q).
- apply: (@repr_mem S F Z cZ T q). exact: double_coset_representative_mem.
- rewrite -preimage_double_coset coset_reprK.
  by rewrite /q double_coset_representative_set.
Qed.

Definition preimage_index (i : double_coset_index P Q T) :
  double_coset_index (preimage P) (preimage Q) (preimage T) :=
  Sub (coset Z @*^-1 val i) (preimage_index_mem i).

Lemma preimage_index_injective : injective preimage_index.
Proof.
move=> i j he; apply: val_inj.
have h := congr1 (fun z : double_coset_index (preimage P) (preimage Q) (preimage T) => val z / Z) he.
by rewrite /= !cosetpreK in h.
Qed.

Lemma preimage_index_surjective j : exists i, preimage_index i = j.
Proof.
pose t := double_coset_representative j.
have tT : t \in preimage T := double_coset_representative_mem j.
have hq : coset Z t \in T by rewrite -(preimage_mem cZ).
have hi : double_coset P Q (coset Z t) \in double_coset P Q @: T.
  apply/imsetP; by exists (coset Z t).
exists (Sub (double_coset P Q (coset Z t)) hi); apply: val_inj.
change (coset Z @*^-1 double_coset P Q (coset Z t) = val j).
rewrite preimage_double_coset; exact: double_coset_representative_set.
Qed.

Lemma quotient_index_exists j : exists i, preimage_index i == j.
Proof. by have [i hi] := preimage_index_surjective j; exists i; rewrite hi. Qed.
Definition quotient_index j := xchoose (quotient_index_exists j).
Lemma preimage_index_quotient j : preimage_index (quotient_index j) = j.
Proof. exact: eqP (xchooseP (quotient_index_exists j)). Qed.
Lemma quotient_index_preimage i : quotient_index (preimage_index i) = i.
Proof. apply: preimage_index_injective; exact: preimage_index_quotient. Qed.
Lemma preimage_index_bijective : bijective preimage_index.
Proof. exists quotient_index; [exact: quotient_index_preimage | exact: preimage_index_quotient]. Qed.

Lemma preimage_representative i :
  double_coset (preimage P) (preimage Q) (double_coset_representative (preimage_index i)) =
  double_coset (preimage P) (preimage Q) (fingroup.repr (double_coset_representative i)).
Proof.
rewrite double_coset_representative_set /= -preimage_double_coset coset_reprK.
by rewrite double_coset_representative_set.
Qed.
End Correspondence.
End DPFusionQuotientDoubleCosets.


