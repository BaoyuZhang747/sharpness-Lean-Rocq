From mathcomp Require Import all_ssreflect all_fingroup center pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionConjugacy FusionAutomorphisms FusionCentricCriterion
  FusionQuotientMaps FusionQuotientConstruction FusionQuotientNormalization
  FusionQuotientAutomorphisms.
Import DPFusion DPFusionQuotientConstruction DPFusionQuotientAutomorphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientCentric.
Section CentricConjugacy.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Lemma centric_conjugate (P Q : {group S}) :
  DPFusionSystem.conjugate F P Q ->
  DPFusionSystem.centric F P -> DPFusionSystem.centric F Q.
Proof.
move=> hPQ hP; apply/forallP=> R; apply/implyP=> hQR.
exact: implyP (forallP hP R) (DPFusionConjugacy.conjugate_trans hPQ hQR).
Qed.

End CentricConjugacy.

Section QuotientCentric.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.

Lemma quotient_selfcentralizing_preimage (P : {group coset_of Z}) :
  'C(P) \subset P -> 'C(preimage P) \subset preimage P.
Proof.
move=> sCP.
have hc : coset Z @* 'C(preimage P) \subset 'C(P).
  have h := morphim_cent (coset_morphism Z) (preimage P).
  change (is_true (coset Z @* 'C(preimage P) \subset 'C(preimage P / Z))) in h.
  by rewrite /preimage /= cosetpreK in h.
apply/subsetP=> s Cs; rewrite (preimage_mem cZ).
apply: (subsetP sCP); apply: (subsetP hc).
apply/morphimP; exists s=> //; exact: normZ_all cZ s.
Qed.

Lemma centric_preimage (P : {group coset_of Z}) :
  DPFusionSystem.centric (system cZ) P ->
  DPFusionSystem.centric F (preimage P).
Proof.
move=> hP; apply/forallP=> Q; apply/implyP=> hPQ.
have sZQ := DPFusionQuotientNormalization.conjugate_contains_kernel cZ
  (kernel_sub_preimage P) hPQ.
have preQ := DPFusionQuotientNormalization.preimage_of_quotient cZ sZQ.
have hbar : DPFusionSystem.conjugate (system cZ) P (Q / Z)%G.
  by rewrite DPFusionQuotientNormalization.conjugate_preimages preQ.
have hQ := implyP (forallP hP (Q / Z)%G) hbar.
have hpre := quotient_selfcentralizing_preimage hQ.
by rewrite preQ in hpre.
Qed.

Lemma kernel_iff (P : {group coset_of Z}) (a : {perm S}) :
  a \in 'ker (automorphism_morphism cZ P) <->
  a \in DPFusionSaturation.aut_group F (preimage P) /\
    {in preimage P, forall x, coset Z (a x) = coset Z x}.
Proof.
split.
- move=> aK; have aA := subsetP (morphpre_sub (automorphism_morphism cZ P) 1) a aK.
  split=> // x xP.
  rewrite -(automorphismE cZ aA xP).
  change (automorphism_morphism cZ P a (coset Z x) = coset Z x).
  by rewrite (mker aK) perm1.
- move=> [aA ha]; apply/morphpreP; split=> //; apply/set1P.
  apply: (eq_Aut (automorphism_in_Aut cZ aA) (group1 (Aut P))).
  move=> q Pq; have xP := repr_mem cZ Pq.
  by rewrite -(coset_reprK q) (automorphismE cZ aA xP) ha // perm1.
Qed.

Lemma normalized_kernel_inner (P : {group coset_of Z}) (p : nat) :
  p.-group Z -> DPFusionSaturation.saturated F p ->
  DPFusionSystem.fully_normalized (system cZ) P ->
  DPFusionSystem.centric (system cZ) P ->
  'ker (automorphism_morphism cZ P) \subset (conj_aut (preimage P) @* preimage P).
Proof.
move=> pZ sat hN hC; apply/subsetP=> a aK.
have aU := subsetP (@kernel_sub_ambient S F Z cZ P p pZ sat hN) a aK.
have /morphimP[s Ns _ ea] := aU.
have sC : coset Z s \in 'C(P).
  apply/centP=> q Pq.
  have ha := congr1 (fun b : {perm coset_of Z} => b q) (mker aK).
  change (automorphism cZ P a q = (1 : {perm coset_of Z}) q) in ha.
  rewrite perm1 in ha.
  have Nsbar := coset_normalizes cZ Ns.
  rewrite ea (automorphism_conjugation cZ Ns) norm_conj_autE
    // in ha.
  apply: esym; apply/commgP/conjg_fixP; exact: ha.
have sP : s \in preimage P.
  rewrite (preimage_mem cZ).
  exact: subsetP (DPFusionCentricCriterion.centric_self_centralizing hC) _ sC.
apply/morphimP; by exists s.
Qed.

End QuotientCentric.
End DPFusionQuotientCentric.
