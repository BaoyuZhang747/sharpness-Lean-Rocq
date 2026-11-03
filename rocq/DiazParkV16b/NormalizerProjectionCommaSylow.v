(** Actual Sylow adjustment inside a prescribed target automorphism subgroup.
    The adjusted map extends over the source K-normalizer; no extension or
    Sylow-comparison law is assumed. *)
From mathcomp Require Import all_boot all_fingroup pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionConjugacy
  FusionAutomorphisms FusionSylowAdjustment FusionKNormalization GroupKNormalizer
  FusionCentricCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionAutomorphisms DPFusionSylowAdjustment.
Local Open Scope group_scope.

Module DPNormalizerProjectionCommaSylow.
Section Domain.
Variable S : finGroupType.
Variables P Q : {group S}.
Variable f : DPFusion.map P Q.
Variable K : {group {perm S}}.

Lemma k_normalizer_sub_extension_domain :
  aut_transport_group f (DPFusionSaturation.ambient_aut_group P :&: K)%G \subset
    DPFusionSaturation.ambient_aut_group Q ->
  k_normalizer [set: S]%G P K \subset DPFusionSaturation.extension_domain f.
Proof.
move=> hT; apply/subsetP=> s /morphpreP[hs ha].
have Ns : s \in 'N(P) by move: hs; rewrite inE inE /=.
change (is_true (conj_aut P s \in K)) in ha.
apply/setIdP; split=> //.
have As : conj_aut P s \in DPFusionSaturation.ambient_aut_group P.
  by apply/morphimP; exists s.
have Ds : conj_aut P s \in (DPFusionSaturation.ambient_aut_group P :&: K)%G.
  by rewrite inE As ha.
have Aps : conj_aut P s \in Aut P := Aut_aut _ _.
have Ts : aut_transport f (conj_aut P s) \in
    aut_transport_group f (DPFusionSaturation.ambient_aut_group P :&: K)%G.
  by apply/morphimP; exists (conj_aut P s).
have /morphimP[t Nt _ ht] := subsetP hT _ Ts.
apply/exists_inP; exists t=> //; apply/forall_inP=> x Px; apply/eqP.
have h1 := aut_transportE f Aps Px.
rewrite norm_conj_autE // in h1.
have h2 := congr1 (fun b : {perm S} => b (f x)) ht.
rewrite norm_conj_autE ?DPFusion.map_into // in h2.
exact: eq_trans (esym h1) h2.
Qed.
End Domain.

Section Adjustment.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Variable hS : p.-group [set: S].
Variables P Q : {group S}.
Variable f : DPFusion.map P Q.
Variable hf : DPFusionSystem.allowed F f.
Variable onto : image f = Q.
Variables K T : {group {perm S}}.
Variable sTF : T \subset DPFusionSaturation.aut_group F Q.
Variable hKT : aut_transport_group f K \subset T.
Variable sylT : p.-Sylow(T) (DPFusionSaturation.ambient_aut_group Q :&: T).

Theorem exists_stabilizer_adjustment :
  exists a : {perm S}, a \in T /\ exists g : DPFusion.map P Q,
    DPFusionSystem.allowed F g /\ image g = Q /\
    {in P, forall x, g x = a (f x)} /\
    k_normalizer [set: S]%G P K \subset DPFusionSaturation.extension_domain g.
Proof.
pose D := (DPFusionSaturation.ambient_aut_group P :&: K)%G.
have sDT : aut_transport_group f D \subset T :=
  subset_trans (morphimS _ (subsetIr _ _)) hKT.
have pD : p.-group D := DPFusionKNormalization.k_automizer_pgroup P K hS.
have pTD : p.-group (aut_transport_group f D) := morphim_pgroup _ pD.
have [a ha hsub] := Sylow_Jsub sylT sDT pTD.
have Fa := subsetP sTF _ ha.
have Aa := subsetP (DPFusionSaturation.aut_group_sub F Q) _ Fa.
pose g := DPFusion.compose f (aut_to_map Aa).
exists a; split=> //; exists g; split.
- exact: DPFusionSystem.composition_closed hf (aut_to_map_allowed Aa Fa).
- split; first exact: DPFusionConjugacy.compose_onto onto (endomorphism_image (aut_to_map Aa)).
  split.
  + move=> x hx; by rewrite /g compose_in // aut_to_mapE ?map_into.
  + apply: k_normalizer_sub_extension_domain.
    rewrite /g (aut_transport_group_comp_aut onto Aa).
    exact: subset_trans hsub (subsetIl _ _).
Qed.

Variable sat : DPFusionSaturation.saturated F p.
Variable centricQ : DPFusionSystem.centric F Q.

Theorem exists_stabilizer_adjusted_extension :
  exists a : {perm S}, a \in T /\ exists (V : {group S})
    (g : DPFusion.map V [set: S]%G),
    P \subset V /\ k_normalizer [set: S]%G P K \subset V /\
    DPFusionSystem.allowed F g /\ {in P, forall x, g x = a (f x)}.
Proof.
have [a [ha [g [hg [og [he hd]]]]]] := exists_stabilizer_adjustment.
have [gh [hgh hext]] := DPFusionSaturation.saturation_extension sat hg og
  (DPFusionCentricCriterion.centric_fully_centralized centricQ).
exists a; split=> //; exists (DPFusionSaturation.extension_domain g), gh.
split; first exact: DPFusionSaturation.source_extension_domain.
split=> //; split=> // x hx; by rewrite (hext x hx) (he x hx).
Qed.
End Adjustment.
End DPNormalizerProjectionCommaSylow.
