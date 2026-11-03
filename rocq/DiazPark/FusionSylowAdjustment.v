From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionConjugacy FusionAutomorphisms.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionSylowAdjustment.
Import DPFusionAutomorphisms.

Section TransportComposition.
Variable S : finGroupType.

Lemma aut_transport_comp_aut (P Q : {group S}) (f : DPFusion.map P Q)
    (onto : DPFusion.image f = Q) (a : {perm S}) (ha : a \in Aut Q)
    (b : {perm S}) (hb : b \in Aut P) :
  aut_transport (DPFusion.compose f (aut_to_map ha)) b = (aut_transport f b) ^ a.
Proof.
pose g := DPFusion.compose f (aut_to_map ha).
have ontog : DPFusion.image g = Q :=
  DPFusionConjugacy.compose_onto onto (endomorphism_image (aut_to_map ha)).
have hleft := aut_transport_mem g b.
rewrite ontog in hleft.
have hright : (aut_transport f b) ^ a \in Aut Q.
  have hbf := aut_transport_mem f b.
  rewrite onto in hbf; exact: groupJ hbf ha.
apply: (eq_Aut hleft hright)=> y Qy.
have /morphimP[x Px _ ->] : y \in DPFusion.image g by rewrite ontog.
have Pbx : b x \in P := Aut_closed hb Px.
rewrite (aut_transportE g hb Px) /g !DPFusion.compose_in //.
rewrite !aut_to_mapE ?DPFusion.map_into //.
rewrite DPFusion.map_morphismE DPFusion.compose_in // aut_to_mapE ?DPFusion.map_into // permJ.
by rewrite (aut_transportE f hb Px).
Qed.

Lemma aut_transport_group_comp_aut (P Q : {group S}) (f : DPFusion.map P Q)
    (onto : DPFusion.image f = Q) (a : {perm S}) (ha : a \in Aut Q)
    (K : {group {perm S}}) :
  aut_transport_group (DPFusion.compose f (aut_to_map ha)) K =
  (aut_transport_group f K :^ a)%G.
Proof.
apply: val_inj; apply/setP=> b; apply/idP/idP.
- move=> /morphimP[c Ac Kc ->].
  change (aut_transport (DPFusion.compose f (aut_to_map ha)) c \in
    aut_transport_group f K :^ a).
  rewrite (aut_transport_comp_aut onto ha Ac).
  apply/imsetP; exists (aut_transport f c)=> //.
  by apply/morphimP; exists c.
- move=> /imsetP[c /morphimP[b0 Ab0 Kb0 ->] ->].
  apply/morphimP; exists b0=> //.
  exact: esym (aut_transport_comp_aut onto ha Ab0).
Qed.

Lemma ambient_aut_pgroup (p : nat) (P : {group S}) :
  p.-group [set: S] -> p.-group (DPFusionSaturation.ambient_aut_group P).
Proof.
move=> hS; apply: morphim_pgroup.
exact: pgroupS (subsetT 'N(P)) hS.
Qed.

Lemma extension_domain_full_of_transport (P Q : {group S}) (f : DPFusion.map P Q) :
  aut_transport_group f (DPFusionSaturation.ambient_aut_group P) \subset
    DPFusionSaturation.ambient_aut_group Q ->
  DPFusionSaturation.extension_domain f = 'N(P)%G.
Proof.
move=> hT; apply: val_inj; apply/eqP; rewrite eqEsubset; apply/andP; split.
- exact: DPFusionSaturation.extension_domain_normalizer.
- apply/subsetP=> s Ns; apply/setIdP; split=> //.
  have As : conj_aut P s \in DPFusionSaturation.ambient_aut_group P.
    by apply/morphimP; exists s.
  have Aps : conj_aut P s \in Aut P := Aut_aut _ _.
  have Ts : aut_transport f (conj_aut P s) \in
      aut_transport_group f (DPFusionSaturation.ambient_aut_group P).
    by apply/morphimP; exists (conj_aut P s).
  have /morphimP[t Nt _ ht] := subsetP hT _ Ts.
  apply/exists_inP; exists t=> //; apply/forall_inP=> x Px; apply/eqP.
  have h1 := aut_transportE f Aps Px.
  rewrite norm_conj_autE // in h1.
  have h2 := congr1 (fun b : {perm S} => b (f x)) ht.
  rewrite norm_conj_autE ?DPFusion.map_into // in h2.
  exact: eq_trans (esym h1) h2.
Qed.

End TransportComposition.

Section SylowAdjustment.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.

(** Sylow adjustment uses only full automization of the target, not saturation. *)
Theorem sylow_adjust_transport (P Q : {group S}) (f : DPFusion.map P Q)
    (H : {group {perm S}}) :
  DPFusionSystem.allowed F f -> DPFusion.image f = Q ->
  H \subset DPFusionSaturation.aut_group F P -> p.-group H ->
  p.-Sylow(DPFusionSaturation.aut_group F Q)
    (DPFusionSaturation.ambient_aut_group Q) ->
  exists g : DPFusion.map P Q,
    DPFusionSystem.allowed F g /\ DPFusion.image g = Q /\
      aut_transport_group g H \subset DPFusionSaturation.ambient_aut_group Q.
Proof.
move=> hf onto sHF pH sylQ.
have sTQ : aut_transport_group f H \subset DPFusionSaturation.aut_group F Q.
  have h := aut_transport_group_sub hf sHF.
  by rewrite onto in h.
have pT : p.-group (aut_transport_group f H) := morphim_pgroup _ pH.
have [a Fa ha] := Sylow_Jsub sylQ sTQ pT.
have Aa : a \in Aut Q := subsetP (DPFusionSaturation.aut_group_sub F Q) a Fa.
exists (DPFusion.compose f (aut_to_map Aa)); split.
- apply: (@DPFusionSystem.composition_closed S F P Q Q f (aut_to_map Aa) hf).
  exact: (@aut_to_map_allowed S F Q a Aa Fa).
- split.
  + exact: DPFusionConjugacy.compose_onto onto (endomorphism_image (aut_to_map Aa)).
  + by rewrite (aut_transport_group_comp_aut onto Aa).
Qed.

Theorem sylow_adjust_normalizer (P Q : {group S}) (f : DPFusion.map P Q) :
  p.-group [set: S] -> DPFusionSystem.allowed F f -> DPFusion.image f = Q ->
  p.-Sylow(DPFusionSaturation.aut_group F Q)
    (DPFusionSaturation.ambient_aut_group Q) ->
  exists g : DPFusion.map P Q,
    DPFusionSystem.allowed F g /\ DPFusion.image g = Q /\
      DPFusionSaturation.extension_domain g = 'N(P)%G.
Proof.
move=> hS hf onto sylQ.
have [g [hg [ontog hT]]] := @sylow_adjust_transport P Q f
  (DPFusionSaturation.ambient_aut_group P) hf onto
  (DPFusionSaturation.ambient_aut_sub F P) (ambient_aut_pgroup P hS) sylQ.
exists g; split=> //; split=> //.
exact: extension_domain_full_of_transport hT.
Qed.

End SylowAdjustment.
End DPFusionSylowAdjustment.
