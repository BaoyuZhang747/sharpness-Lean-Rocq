From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionConjugacy.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAutomorphisms.
Section NativeAutomorphisms.
Variable S : finGroupType.

Lemma endomorphism_image (P : {group S}) (f : DPFusion.map P P) :
  DPFusion.image f = P.
Proof.
apply: val_inj; apply/eqP; rewrite eqEcard; apply/andP; split.
- exact: DPFusion.image_sub.
- by rewrite DPFusionConjugacy.map_image_card.
Qed.

Lemma endomorphism_image_set (P : {group S}) (f : DPFusion.map P P) :
  DPFusion.map_morphism f @* P = P.
Proof.
change (val (DPFusion.image f) = val P).
by rewrite endomorphism_image.
Qed.

Definition map_aut (P : {group S}) (f : DPFusion.map P P) : {perm S} :=
  aut (DPFusion.map_injm f) (endomorphism_image_set f).

Lemma map_autE (P : {group S}) (f : DPFusion.map P P) : {in P, map_aut f =1 f}.
Proof. exact: autE. Qed.

Lemma map_aut_mem (P : {group S}) (f : DPFusion.map P P) : map_aut f \in Aut P.
Proof. exact: Aut_aut. Qed.

Definition aut_to_map (P : {group S}) (a : {perm S}) (ha : a \in Aut P) :
    DPFusion.map P P.
Proof.
apply: (@DPFusion.of_morphism S P P [morphism of autm ha] (injm_autm ha)).
by rewrite im_autm.
Defined.

Lemma aut_to_mapE (P : {group S}) (a : {perm S}) (ha : a \in Aut P) :
  {in P, aut_to_map ha =1 a}.
Proof. exact: DPFusion.normalize_in. Qed.

Lemma map_aut_to_map (P : {group S}) (a : {perm S}) (ha : a \in Aut P) :
  map_aut (aut_to_map ha) = a.
Proof.
apply: (eq_Aut (map_aut_mem _) ha)=> x Px.
by rewrite map_autE // aut_to_mapE.
Qed.

Definition aut_transport (P Q : {group S}) (f : DPFusion.map P Q) :=
  Aut_isom (DPFusion.map_injm f) (subxx P).

Lemma aut_transportE (P Q : {group S}) (f : DPFusion.map P Q)
    (a : {perm S}) :
  a \in Aut P -> {in P, forall x, aut_transport f a (f x) = f (a x)}.
Proof. exact: Aut_isomE. Qed.

Lemma aut_transport_mem (P Q : {group S}) (f : DPFusion.map P Q) a :
  aut_transport f a \in Aut (DPFusion.image f).
Proof. exact: Aut_Aut_isom. Qed.

Definition aut_transport_group (P Q : {group S}) (f : DPFusion.map P Q)
    (K : {group {perm S}}) : {group {perm S}} :=
  (Aut_isom (DPFusion.map_injm f) (subxx P) @* K)%G.

Lemma aut_transport_group_card (P Q : {group S}) (f : DPFusion.map P Q)
    (K : {group {perm S}}) :
  K \subset Aut P -> #|aut_transport_group f K| = #|K|.
Proof.
move=> sKA; apply: card_injm sKA.
exact: injm_Aut_isom.
Qed.

End NativeAutomorphisms.

Section AllowedAutomorphisms.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Lemma map_aut_allowed (P : {group S}) (f : DPFusion.map P P) :
  DPFusionSystem.allowed F f -> map_aut f \in DPFusionSaturation.aut_group F P.
Proof.
move=> hf; apply/setIdP; split; first exact: map_aut_mem.
apply/existsP; exists f; apply/andP; split=> //.
by apply/forall_inP=> x Px; rewrite map_autE.
Qed.

Lemma aut_to_map_allowed (P : {group S}) (a : {perm S}) (ha : a \in Aut P) :
  a \in DPFusionSaturation.aut_group F P ->
  DPFusionSystem.allowed F (aut_to_map ha).
Proof.
move=> /setIdP[_ /existsP[f /andP[hf /forall_inP heq]]].
have h : aut_to_map ha = f.
  apply: DPFusion.map_ext=> x Px.
  by rewrite aut_to_mapE // (eqP (heq x Px)).
by rewrite h.
Qed.

Lemma aut_transport_allowed (P Q : {group S}) (f : DPFusion.map P Q) a :
  DPFusionSystem.allowed F f -> a \in DPFusionSaturation.aut_group F P ->
  aut_transport f a \in DPFusionSaturation.aut_group F (DPFusion.image f).
Proof.
move=> hf /setIdP[Aa /existsP[b /andP[hb /forall_inP heb]]].
apply/setIdP; split; first exact: aut_transport_mem.
pose c := DPFusion.compose (DPFusion.compose (DPFusion.inverse f) b) (DPFusion.to_image f).
apply/existsP; exists c; apply/andP; split.
- apply: DPFusionSystem.composition_closed; last exact: DPFusionSystem.image_closed hf.
  apply: DPFusionSystem.composition_closed hb.
  exact: DPFusionSystem.inverse_closed hf.
- apply/forall_inP=> y Iy; apply/eqP.
  have /morphimP[x Px _ ->] := Iy.
  have Ifx := DPFusion.image_mem f Px.
  rewrite /c !DPFusion.compose_in // DPFusion.to_image_in ?DPFusion.map_into //.
  rewrite DPFusion.inverse_cancel // (eqP (heb x Px)).
  exact: esym (aut_transportE f Aa Px).
Qed.

Lemma aut_transport_group_sub (P Q : {group S}) (f : DPFusion.map P Q)
    (K : {group {perm S}}) :
  DPFusionSystem.allowed F f -> K \subset DPFusionSaturation.aut_group F P ->
  aut_transport_group f K \subset DPFusionSaturation.aut_group F (DPFusion.image f).
Proof.
move=> hf sKF; apply/subsetP=> b /morphimP[a _ Ka ->].
exact: (@aut_transport_allowed P Q f a hf (subsetP sKF a Ka)).
Qed.

End AllowedAutomorphisms.
End DPFusionAutomorphisms.
