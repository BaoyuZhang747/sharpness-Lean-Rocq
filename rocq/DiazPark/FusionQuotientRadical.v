From mathcomp Require Import all_ssreflect all_fingroup center pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionConjugacy FusionAutomorphisms FusionCentricBasics FusionCentricCriterion
  FusionOuterAutomorphisms FusionRadical FusionQuotientMaps FusionQuotientConstruction
  FusionQuotientNormalization FusionQuotientAutomorphisms FusionQuotientCentric
  FusionQuotientCentricTransport FusionQuotientCollection FusionQuotientCollectionClosure.
Import DPFusion DPFusionQuotientConstruction DPFusionQuotientNormalization
  DPFusionQuotientAutomorphisms DPFusionQuotientCentric
  DPFusionQuotientCentricTransport DPFusionQuotientCollection
  DPFusionQuotientCollectionClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientRadical.
Section Radical.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable p : nat.
Hypothesis pZ : p.-group Z.

Lemma radical_kernel_inner (P : {group coset_of Z}) :
  DPFusionRadical.radical F p (preimage P) ->
  'ker (automorphism_morphism cZ P) \subset DPFusionOuter.inner (preimage P).
Proof.
move=> hP; apply: DPFusionRadical.radical_normal_p_sub_inner hP _ _.
- exact: (@automorphism_kernel_pgroup S F Z cZ P p pZ).
- exact: ker_normal.
Qed.

(** A centric full preimage whose quotient kernel is inner has a
    self-centralizing quotient. *)
Lemma inner_kernel_selfcentralizing (P : {group coset_of Z}) :
  DPFusionSystem.centric F (preimage P) ->
  'ker (automorphism_morphism cZ P) \subset DPFusionOuter.inner (preimage P) ->
  'C(P) \subset P.
Proof.
move=> hP hK; apply/subsetP=> q Cq.
pose s := fingroup.repr q.
have sq : coset Z s = q := coset_reprK q.
have Ns : s \in 'N(preimage P).
  change (is_true (s \in ('N(preimage P)%G))).
  rewrite -(normalizer_preimage cZ P) (preimage_mem cZ) sq.
  exact: subsetP (cent_sub P) q Cq.
have aA : conj_aut (preimage P) s \in DPFusionSaturation.aut_group F (preimage P).
  apply: (subsetP (DPFusionSaturation.ambient_aut_sub F (preimage P))).
  apply/morphimP; by exists s.
have aK : conj_aut (preimage P) s \in 'ker (automorphism_morphism cZ P).
  apply: (proj2 (kernel_iff cZ P _)); split=> // x Px.
  rewrite norm_conj_autE //.
  have hj := morphJ (coset_morphism Z) (normZ_all cZ x) (normZ_all cZ s).
  change (coset Z (x ^ s) = (coset Z x) ^ (coset Z s)) in hj.
  rewrite hj sq.
  apply/conjg_fixP/commgP.
  have qx : coset Z x \in P by move: Px; rewrite (preimage_mem cZ).
  exact: esym (centP Cq (coset Z x) qx).
have /morphimP[r Nr Pr er] := subsetP hK _ aK.
have sc : s * r^-1 \in 'C(preimage P).
  apply/centP=> x Px; apply: esym; apply/commgP/conjg_fixP.
  rewrite conjgM.
  have he := congr1 (fun a : {perm S} => a x) er.
  rewrite !norm_conj_autE // in he.
  by rewrite he conjgK.
have srP := subsetP (DPFusionCentricCriterion.centric_self_centralizing hP) _ sc.
have sP : s \in preimage P.
  have hsm := groupM srP Pr; by rewrite mulgKV in hsm.
by move: sP; rewrite (preimage_mem cZ) sq.
Qed.

Theorem centric_radical_preimage (P : {group coset_of Z}) :
  DPFusionSystem.centric F (preimage P) ->
  DPFusionRadical.radical F p (preimage P) ->
  DPFusionSystem.centric (system cZ) P.
Proof.
move=> hC hR; apply/forallP=> Q; apply/implyP=> hPQ.
have hpre : DPFusionSystem.conjugate F (preimage P) (preimage Q).
  by rewrite -conjugate_preimages.
have hCQ := DPFusionCentricBasics.centric_conjugate hpre hC.
have /existsP[g /andP[Fg /eqP onto]] := DPFusionConjugacy.conjugate_reverse hpre.
apply: inner_kernel_selfcentralizing hCQ _.
apply/subsetP=> a aK.
have aA := subsetP (morphpre_sub (automorphism_morphism cZ Q) 1) a aK.
have aAut := subsetP (DPFusionSaturation.aut_group_sub F (preimage Q)) a aA.
have gK := kernel_transport Fg onto aK.
have gi := subsetP (radical_kernel_inner hR) _ gK.
apply: (@aut_transport_inner_reflect S (preimage Q) (preimage P) g a aAut).
by rewrite onto.
Qed.

Theorem centric_radical_collection (P : {group S}) :
  DPFusionSystem.centric F P -> DPFusionRadical.radical F p P -> collection cZ P.
Proof.
move=> hC hR.
have sZP := centric_contains_center cZ hC.
rewrite /collection sZP /=.
apply: centric_radical_preimage; by rewrite (preimage_of_quotient cZ sZP).
Qed.
End Radical.
End DPFusionQuotientRadical.

Print Assumptions DPFusionQuotientRadical.centric_radical_collection.
