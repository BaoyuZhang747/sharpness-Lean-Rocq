From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionAutomorphisms
  FusionCentralizerMaps FusionCentralizer FusionCentralizerExtension FusionCentralizerAut
  FusionCentralizerAutRestriction GroupKNormalizer FusionKNormalization.
Import DPFusion DPFusionSubgroup DPFusionCentralizerAut DPFusionCentralizerAutRestriction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentralizerAutNormalizer.
Section Normalizer.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Local Notation C := 'C(E)%G.
Local Notation T := [subg C]%type.
Local Notation J P := (DPFusionCentralizer.joint (E := E) P).
Variable P : {group T}.

Lemma k_normalizerE :
  k_normalizer [set: S] (J P) (K F E P) = ambient 'N(P)%G.
Proof.
apply: val_inj; apply/setP=> s; apply/idP/idP.
- case/morphpreP=> Ns Ka.
  have NsJ : s \in 'N(J P) by move: Ns; rewrite inE inE /=.
  change (is_true (conj_aut (J P) s \in K F E P)) in Ka.
  have Cs : s \in C.
    apply/centP=> e Ee.
    have Je := subsetP (DPFusionCentralizer.joint_right P) e Ee.
    have he := @K_fixes S F E P _ Ka e Ee.
    rewrite norm_conj_autE // in he.
    apply: (mulgI s^-1); by rewrite mulgA mulVg mul1g -conjgE he.
  have Nv : subg C s \in 'N(P).
    rewrite inE; apply/subsetP=> y /imsetP[x Px ->].
    have Jx := subsetP (DPFusionCentralizer.joint_left P) _ (ambient_mem Px).
    have hs := @K_preserves S F E P _ Ka (val x) (ambient_mem Px).
    rewrite norm_conj_autE // in hs.
    have h := ambient_repr hs.
    have ev : subg C ((val x) ^ s) = x ^ (subg C s).
      apply: val_inj; rewrite (ambient_subgK hs).
      by change (val x ^ s = val x ^ val (subg C s)); rewrite subgK.
    by rewrite -ev.
  have := ambient_mem Nv; by rewrite subgK.
- case/morphimP=> t _ Nt ->.
  apply/morphpreP; split.
  + by rewrite inE inE /=; exact: DPFusionCentralizerExtension.joint_normalizer Nt.
  + change (conj_aut (J P) (val t) \in K F E P).
    have NtJ := DPFusionCentralizerExtension.joint_normalizer (E := E) Nt.
    apply/setIdP; split.
    * apply: (subsetP (DPFusionSaturation.ambient_aut_sub F (J P)) (conj_aut (J P) (val t))).
      by apply/morphimP; exists (val t).
    * apply/andP; split; apply/forall_inP=> x Px.
      -- have Jx := subsetP (DPFusionCentralizer.joint_left P) x Px.
         rewrite norm_conj_autE // -(ambient_subgK Px).
         change (val ((subg C x) ^ t) \in ambient P).
         apply: ambient_mem; rewrite memJ_norm //; exact: ambient_repr Px.
      -- apply/eqP; rewrite norm_conj_autE //.
         ++ by rewrite conjgE -(centP (valP t) x Px) mulKg.
         ++ exact: subsetP (DPFusionCentralizer.joint_right P) x Px.
Qed.

Lemma normalizer_conjugation_K (t : T) :
  t \in 'N(P) -> conj_aut (J P) (val t) \in K F E P.
Proof.
move=> Nt; have ht := ambient_mem Nt.
rewrite -k_normalizerE in ht.
by case/morphpreP: ht=> _ ht.
Qed.

Lemma restriction_conjugation (t : T) :
  t \in 'N(P) -> (@restriction S F E P) (conj_aut (J P) (val t)) = conj_aut P t.
Proof.
move=> Nt.
have NtJ := DPFusionCentralizerExtension.joint_normalizer (E := E) Nt.
have Ka := normalizer_conjugation_K Nt.
apply: (eq_Aut ((@restriction_Aut S F E P) _) (Aut_aut _ _))=> x Px.
apply: val_inj; rewrite restrictionE // !norm_conj_autE //.
exact: subsetP (DPFusionCentralizer.joint_left P) _ (ambient_mem Px).
Qed.

Lemma restriction_ambient_aut_image :
  (@restriction_morphism S F E P) @*
    (DPFusionSaturation.ambient_aut_group (J P) :&: K F E P) =
  DPFusionSaturation.ambient_aut_group P.
Proof.
apply/setP=> b; apply/idP/idP.
- case/morphimP=> a _ /setIP[/morphimP[s Ns _ ea] Ka] ->.
  subst a.
  have hs : s \in k_normalizer [set: S] (J P) (K F E P).
    apply/morphpreP; split; last exact Ka.
    by rewrite inE inE /=.
  rewrite k_normalizerE in hs.
  have Nt := ambient_repr hs.
  change ((@restriction S F E P) (conj_aut (J P) s) \in DPFusionSaturation.ambient_aut_group P).
  rewrite -(ambient_subgK hs) restriction_conjugation //.
  by apply/morphimP; exists (subg C s).
- case/morphimP=> t Nt _ ->.
  have Ka := normalizer_conjugation_K Nt.
  apply/morphimP; exists (conj_aut (J P) (val t)); first exact Ka.
  + apply/setIP; split; last exact Ka.
    apply/morphimP; exists (val t)=> //;
      exact: DPFusionCentralizerExtension.joint_normalizer Nt.
  + symmetry; exact: restriction_conjugation Nt.
Qed.

Lemma restriction_sylow (p : nat) :
  p.-Sylow(K F E P)
    (DPFusionSaturation.ambient_aut_group (J P) :&: K F E P) ->
  p.-Sylow(DPFusionSaturation.aut_group (DPFusionCentralizer.system F E) P)
    (DPFusionSaturation.ambient_aut_group P).
Proof.
move=> syl; have h := morphim_pHall (@restriction_morphism S F E P) (subsetIr (DPFusionSaturation.ambient_aut_group (J P)) (K F E P)) syl.
rewrite restriction_image restriction_ambient_aut_image in h.
exact h.
Qed.

End Normalizer.
End DPFusionCentralizerAutNormalizer.










