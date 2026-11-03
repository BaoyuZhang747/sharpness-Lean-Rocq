From mathcomp Require Import all_boot all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionConjugacy
  FusionAutomorphisms FusionOuterAutomorphisms FusionRadical.
Import DPFusion DPFusionAutomorphisms DPFusionOuter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAtomicConjugacy.
Section Transport.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q : {group S}.
Variable f : DPFusion.map P Q.
Hypothesis hf : DPFusionSystem.allowed F f.
Hypothesis onto : DPFusion.image f = Q.

Lemma transport_group :
  aut_transport_group f (DPFusionSaturation.aut_group F P) = DPFusionSaturation.aut_group F Q.
Proof.
apply: val_inj; apply/setP=> b; apply/idP/idP.
- move=> /morphimP[a _ ha ->].
  have h := aut_transport_allowed hf ha; by rewrite onto in h.
- move=> hb.
  have bAut := subsetP (DPFusionSaturation.aut_group_sub F Q) b hb.
  pose g := DPFusionConjugacy.onto_inverse onto.
  have hg : DPFusionSystem.allowed F g := DPFusionConjugacy.onto_inverse_allowed onto hf.
  have ontog : DPFusion.image g = P := DPFusionConjugacy.onto_inverse_image onto.
  pose a := aut_transport g b.
  have ha : a \in DPFusionSaturation.aut_group F P.
    have h := aut_transport_allowed hg hb; by rewrite ontog in h.
  have aAut := subsetP (DPFusionSaturation.aut_group_sub F P) a ha.
  have e : aut_transport f a = b.
    have hAut := aut_transport_mem f a; rewrite onto in hAut.
    apply: (eq_Aut hAut bAut)=> y Qy.
    have Py := DPFusion.map_into g Qy.
    rewrite -(DPFusionConjugacy.onto_inverse_cancel_right onto Qy).
    rewrite aut_transportE //.
    rewrite /a aut_transportE //.
    by rewrite /g !DPFusionConjugacy.onto_inverse_cancel_right ?Aut_closed.
  apply/morphimP; exists a=> //.
Qed.

Lemma transport_conjugation x : x \in P ->
  aut_transport f (conj_aut P x) = conj_aut Q (f x).
Proof.
move=> Px.
have hAut := aut_transport_mem f (conj_aut P x); rewrite onto in hAut.
apply: (eq_Aut hAut (Aut_aut _ _))=> y Qy.
have Iy : y \in DPFusion.image f by rewrite onto.
have /morphimP[z Pz _ ->] := Iy.
rewrite aut_transportE ?Aut_aut // !norm_conj_autE
  ?(subsetP (normG P) _ Px) ?(subsetP (normG Q) _ (DPFusion.map_into f Px)) //.
- exact (morphJ (DPFusion.map_morphism f) Pz Px).
- exact: DPFusion.map_into.
Qed.

Lemma transport_inner : aut_transport_group f (inner P) = inner Q.
Proof.
apply: val_inj; apply/setP=> b; apply/idP/idP.
- move=> /morphimP[a _ /morphimP[x _ Px ->] ->].
  change (aut_transport f (conj_aut P x) \in inner Q).
  rewrite transport_conjugation //.
  exact: mem_morphim (subsetP (normG Q) _ (DPFusion.map_into f Px)) (DPFusion.map_into f Px).
- move=> /morphimP[y _ Qy ->].
  have Iy : y \in DPFusion.image f by rewrite onto.
  have /morphimP[x Px _ ->] := Iy.
  apply/morphimP; exists (conj_aut P x).
  + exact: Aut_aut.
  + exact: mem_morphim (subsetP (normG P) _ Px) Px.
  + exact: esym (transport_conjugation Px).
Qed.

Definition restricted_transport := restrm (DPFusionSaturation.aut_group_sub F P)
  (Aut_isom (DPFusion.map_injm f) (subxx P)).

Lemma restricted_transport_group :
  (restricted_transport @* DPFusionSaturation.aut_group F P)%G = DPFusionSaturation.aut_group F Q.
Proof.
apply: val_inj; change (restricted_transport @* DPFusionSaturation.aut_group F P = DPFusionSaturation.aut_group F Q).
rewrite /restricted_transport morphim_restrm setIid.
exact (congr1 val transport_group).
Qed.
Lemma restricted_transport_inner :
  (restricted_transport @* inner P)%G = inner Q.
Proof.
apply: val_inj; change (restricted_transport @* inner P = inner Q).
rewrite /restricted_transport morphim_restrm (setIidPr (inner_sub F P)).
exact (congr1 val transport_inner).
Qed.

Theorem outer_isog : outer_group F P \isog outer_group F Q.
Proof.
pose q := quotm_morphism restricted_transport (inner_normal F P).
have injq : 'injm q := injm_quotm _ (injm_restrm _ (injm_Aut_isom _ _)).
have h : outer_group F P \isog
    (restricted_transport @* DPFusionSaturation.aut_group F P /
      restricted_transport @* inner P)%G.
  apply/isogP; exists q=> //.
  exact: morphim_quotm.
by rewrite restricted_transport_group restricted_transport_inner in h.
Qed.

Lemma radical_onto p : DPFusionRadical.radical F p P = DPFusionRadical.radical F p Q.
Proof. exact: isog_eq1 (isog_pcore p outer_isog). Qed.
End Transport.

Lemma radical_conjugate (S : finGroupType) (F : DPFusionSystem.system S)
    (p : nat) (P Q : {group S}) : DPFusionSystem.conjugate F P Q ->
    DPFusionRadical.radical F p P = DPFusionRadical.radical F p Q.
Proof.
move=> /existsP[f /andP[hf /eqP onto]].
exact (@radical_onto S F P Q f hf onto p).
Qed.
End DPFusionAtomicConjugacy.












