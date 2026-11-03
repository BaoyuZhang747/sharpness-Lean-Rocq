From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import FusionMaps FusionSystems FusionConjugacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

(** Finite quotient by U-conjugacy, restricted to the subgroups of U in
    the given F-conjugacy class.  A quotient representative is a genuine
    subgroup satisfying both conditions. *)
Module DPSimpleConjugacyIndices.
Section Indices.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables Q U : {group S}.

Definition contained_conjugate :=
  {L : {group S} | (L \subset U) && DPFusionSystem.conjugate F Q L}.
Definition contained_subgroup (L : contained_conjugate) : {group S} := val L.
Lemma contained_le (L : contained_conjugate) : contained_subgroup L \subset U.
Proof. exact: (andP (valP L)).1. Qed.
Lemma contained_fusion (L : contained_conjugate) :
  DPFusionSystem.conjugate F Q (contained_subgroup L).
Proof. exact: (andP (valP L)).2. Qed.

Definition inner_conjugate (L K : contained_conjugate) :=
  [exists t in U, contained_subgroup L :^ t == contained_subgroup K].

Lemma inner_conjugate_refl : reflexive inner_conjugate.
Proof.
move=> L; apply/exists_inP; exists (1 : S); first exact: group1.
by rewrite conjsg1.
Qed.
Lemma inner_conjugate_reverse L K : inner_conjugate L K -> inner_conjugate K L.
Proof.
move=> /exists_inP[t ht /eqP he]; apply/exists_inP; exists t^-1.
- by rewrite groupV.
- by rewrite -he conjsgK.
Qed.
Lemma inner_conjugate_sym : symmetric inner_conjugate.
Proof. move=> L K; apply/idP/idP; exact: inner_conjugate_reverse. Qed.
Lemma inner_conjugate_trans : transitive inner_conjugate.
Proof.
move=> L K H /exists_inP[t ht /eqP he] /exists_inP[s hs /eqP hf].
apply/exists_inP; exists (t * s); first exact: groupM ht hs.
by rewrite conjsgM he hf.
Qed.

Definition conjugacy_equiv :=
  EquivRel inner_conjugate inner_conjugate_refl inner_conjugate_sym inner_conjugate_trans.
Definition conjugacy_index := {eq_quot conjugacy_equiv}.
#[export] HB.instance Definition _ := [Finite of conjugacy_index by <:%/].
Definition conjugacy_class (L : contained_conjugate) : conjugacy_index :=
  \pi_conjugacy_index L.
Definition representative (i : conjugacy_index) : contained_conjugate := repr i.
Definition representative_subgroup (i : conjugacy_index) := contained_subgroup (representative i).
Lemma representative_le i : representative_subgroup i \subset U.
Proof. exact: contained_le. Qed.
Lemma representative_fusion i : DPFusionSystem.conjugate F Q (representative_subgroup i).
Proof. exact: contained_fusion. Qed.

Lemma conjugacy_class_eq L K : reflect (conjugacy_class L = conjugacy_class K)
  (inner_conjugate L K).
Proof. exact: eqmodP. Qed.
Lemma representative_related L : inner_conjugate L (representative (conjugacy_class L)).
Proof.
apply/conjugacy_class_eq; symmetry; exact: reprK.
Qed.
Lemma representatives_distinct i j : i != j ->
  ~~ [exists t in U, representative_subgroup i :^ t == representative_subgroup j].
Proof.
move=> hij; apply/negP=> hc.
have he : conjugacy_class (representative i) = conjugacy_class (representative j).
  apply/conjugacy_class_eq; exact hc.
have hij' : i = j by move: he; rewrite /conjugacy_class /representative !reprK.
by move: hij; rewrite hij' eqxx.
Qed.
End Indices.
End DPSimpleConjugacyIndices.
