From mathcomp Require Import all_ssreflect fingroup perm morphism automorphism.
From mathcomp Require Import quotient cyclic pgroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

(** The K-normalizer is the actual inverse image of K under normalizer
    conjugation.  S may be a subgroup of a larger ambient finite group;
    hence both normalizers and centralizers are explicitly relative to S. *)
Section KNormalizer.
Variable gT : finGroupType.
Variables S P : {group gT}.

Definition ambient_normalizer_conjugation :
    {morphism 'N_S(P) >-> {perm gT}} :=
  [morphism of restrm (subsetIr S 'N(P)) (conj_aut P)].

Definition ambient_automorphism_group : {group {perm gT}} :=
  (ambient_normalizer_conjugation @* 'N_S(P))%G.

Lemma ambient_normalizer_conjugation_kernel :
  'ker ambient_normalizer_conjugation = 'C_S(P).
Proof.
rewrite /ambient_normalizer_conjugation ker_restrm ker_conj_aut.
by rewrite -setIA (setIidPr (cent_sub P)).
Qed.

Lemma ambient_automorphism_group_sub : ambient_automorphism_group \subset Aut P.
Proof.
change ((restrm (subsetIr S 'N(P)) (conj_aut P) @* 'N_S(P)) \subset Aut P).
rewrite morphim_restrm.
exact: Aut_conj_aut.
Qed.

Variable K : {group {perm gT}}.

Definition k_normalizer : {group gT} :=
  (ambient_normalizer_conjugation @*^-1 K)%G.

Definition k_automorphism_group : {group {perm gT}} :=
  (ambient_automorphism_group :&: K)%G.

Lemma k_normalizer_sub : k_normalizer \subset 'N_S(P).
Proof. exact: morphpre_sub. Qed.

Lemma k_normalizer_image :
  ambient_normalizer_conjugation @* k_normalizer = k_automorphism_group.
Proof.
change (ambient_normalizer_conjugation @*
  (ambient_normalizer_conjugation @*^-1 K) =
  (ambient_normalizer_conjugation @* 'N_S(P)) :&: K).
by rewrite -[ambient_normalizer_conjugation @*^-1 K]morphpreIdom
  morphim_setIpre.
Qed.

Lemma k_normalizer_card :
  #|k_normalizer| = (#|'C_S(P)| * #|k_automorphism_group|)%N.
Proof.
change (#|ambient_normalizer_conjugation @*^-1 K| =
  (#|'C_S(P)| * #|(ambient_normalizer_conjugation @* 'N_S(P)) :&: K|)%N).
rewrite -[ambient_normalizer_conjugation @*^-1 K]morphpreIim.
by rewrite card_morphpre ?subsetIl // ambient_normalizer_conjugation_kernel.
Qed.

Lemma k_normalizer_pgroup (pi : nat_pred) :
  pi.-group S -> pi.-group k_normalizer.
Proof.
apply: pgroupS.
exact: subset_trans k_normalizer_sub (subsetIl S 'N(P)).
Qed.

Lemma k_automorphism_group_pgroup (pi : nat_pred) :
  pi.-group S -> pi.-group k_automorphism_group.
Proof.
move=> piS; rewrite -k_normalizer_image.
exact: morphim_pgroup _ (k_normalizer_pgroup piS).
Qed.

End KNormalizer.
