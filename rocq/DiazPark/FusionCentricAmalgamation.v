From mathcomp Require Import all_ssreflect all_fingroup generic_quotient pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit FusionSaturation
  FusionCentricBasics FusionCentricNormalizerExtension FusionCentricRigidity.
Import DPFusion DPFusionOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricAmalgamation.
Section CompatibleGroup.
Variable S : finGroupType.
Variables U T : {group S}.
Variable gamma : DPFusion.map U T.
Definition compatible_set := [set n in 'N(U) |
  [exists t in T, [forall u in U, gamma (u ^ n) == (gamma u) ^ t]]].
Lemma compatible_group_set : group_set compatible_set.
Proof.
apply/group_setP; split.
- apply/setIdP; split; first exact: group1.
  apply/exists_inP; exists (1:S); first exact: group1.
  by apply/forall_inP=> u Uu; rewrite !conjg1.
- move=> n m /setIdP[Nn /exists_inP[s Ts /forall_inP hs]]
    /setIdP[Nm /exists_inP[t Tt /forall_inP ht]].
  apply/setIdP; split; first exact: groupM Nn Nm.
  apply/exists_inP; exists (s*t); first exact: groupM Ts Tt.
  apply/forall_inP=> u Uu.
  have Uun : u ^ n \in U by rewrite memJ_norm.
  by rewrite !conjgM (eqP (ht _ Uun)) (eqP (hs _ Uu)).
Qed.
Definition compatible_group : {group S} := group compatible_group_set.
Lemma compatible_group_normalizes : compatible_group \subset 'N(U).
Proof. by apply/subsetP=> n /setIdP[Nn _]. Qed.
Lemma compatible_group_contains_source : U \subset compatible_group.
Proof.
apply/subsetP=> n Un; apply/setIdP; split; first exact: subsetP (normG U) n Un.
apply/exists_inP; exists (gamma n); first exact: DPFusion.map_into Un.
apply/forall_inP=> u Uu; apply/eqP.
exact (morphJ (DPFusion.map_morphism gamma) Uu Un).
Qed.
Lemma compatible_group_witness n : n \in compatible_group ->
  exists t, t \in T /\ {in U, forall u, gamma (u ^ n) = (gamma u) ^ t}.
Proof.
move=> /setIdP[_ /exists_inP[t Tt /forall_inP ht]].
exists t; split=> // u Uu; exact: eqP (ht u Uu).
Qed.

Lemma extended_normalizer_sub (A : {group S}) (sUA : U \subset A)
    (alpha : DPFusion.map A T) (q : S) :
  q \in T -> {in U, forall u, gamma u = (alpha u) ^ q} ->
  'N_A(U) \subset compatible_group.
Proof.
move=> Tq heq; apply/subsetP=> n /setIP[An Nn].
apply/setIdP; split=> //; apply/exists_inP; exists ((alpha n)^q).
- exact: groupJ (DPFusion.map_into alpha An) Tq.
- apply/forall_inP=> u Uu; apply/eqP.
  have Uun : u ^ n \in U by rewrite memJ_norm.
  rewrite (heq _ Uun) (heq _ Uu).
  have hm : alpha (u ^ n) = (alpha u) ^ (alpha n) :=
    morphJ (DPFusion.map_morphism alpha) (subsetP sUA u Uu) An.
  rewrite hm.
  exact: conjJg.
Qed.

End CompatibleGroup.

Section Amalgamation.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.
Variables U A B T : {group S}.
Hypotheses (sUA : U \subset A) (sUB : U \subset B).
Variable gamma : DPFusion.map U T.
Hypotheses (hg : DPFusionSystem.allowed F gamma) (cU : DPFusionSystem.centric F U).
Variables alpha : DPFusion.map A T.
Variables beta : DPFusion.map B T.
Variables qa qb : S.
Hypotheses (Tqa : qa \in T) (Tqb : qb \in T).
Hypothesis agreeA : {in U, forall u, gamma u = (alpha u) ^ qa}.
Hypothesis agreeB : {in U, forall u, gamma u = (beta u) ^ qb}.

Definition amalgam_domain : {group S} := ('N_A(U) <*> 'N_B(U))%G.
Lemma source_sub_amalgam : U \subset amalgam_domain.
Proof.
apply: subset_trans (joing_subl _ _).
by rewrite subsetI sUA normG.
Qed.
Lemma amalgam_sub_compatible : amalgam_domain \subset compatible_group gamma.
Proof.
rewrite join_subG; apply/andP; split.
- exact (@extended_normalizer_sub S U T gamma A sUA alpha qa Tqa agreeA).
- exact (@extended_normalizer_sub S U T gamma B sUB beta qb Tqb agreeB).
Qed.
Lemma amalgam_normalizes : amalgam_domain \subset 'N(U).
Proof. exact: subset_trans amalgam_sub_compatible (compatible_group_normalizes gamma). Qed.

Theorem normalizer_amalgamation :
  exists delta : DPFusion.map amalgam_domain T,
    DPFusionSystem.allowed F delta /\ {in U, delta =1 gamma}.
Proof.
apply: (@DPFusionCentricNormalizerExtension.centric_normalizer_extension
  S F p sat U amalgam_domain T gamma hg cU source_sub_amalgam amalgam_normalizes).
move=> n Dn; exact: compatible_group_witness (subsetP amalgam_sub_compatible n Dn).
Qed.

End Amalgamation.
End DPFusionCentricAmalgamation.
