From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionSylowAdjustment FusionConjugacy.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionNormalizerExtension.

Section ImageControl.
Variable S : finGroupType.

Lemma extension_maps_normalizer (P Q A : {group S})
    (f : DPFusion.map P Q) (h : DPFusion.map A [set: S]%G)
    (sPA : P \subset A) :
  DPFusion.image f = Q -> {in P, h =1 f} ->
  forall s, s \in A -> s \in 'N(P) -> h s \in 'N(Q).
Proof.
move=> onto hext s As Ns; rewrite inE; apply/subsetP=> y /imsetP[z Qz ->].
have /morphimP[x Px _ hx] : z \in DPFusion.image f by rewrite onto.
have Ax := subsetP sPA x Px.
have Pxs : x ^ s \in P by rewrite memJ_norm.
rewrite hx DPFusion.map_morphismE -(hext x Px).
rewrite -(morphJ (DPFusion.map_morphism h) Ax As) DPFusion.map_morphismE (hext _ Pxs).
exact: DPFusion.map_into Pxs.
Qed.

Lemma extension_maps_centralizer (P Q A : {group S})
    (f : DPFusion.map P Q) (h : DPFusion.map A [set: S]%G)
    (sPA : P \subset A) :
  DPFusion.image f = Q -> {in P, h =1 f} ->
  forall s, s \in A -> s \in 'C(P) -> h s \in 'C(Q).
Proof.
move=> onto hext s As Cs; apply/centP=> y Qy.
have /morphimP[x Px _ hx] : y \in DPFusion.image f by rewrite onto.
have Ax := subsetP sPA x Px.
rewrite hx DPFusion.map_morphismE -(hext x Px) /commute.
rewrite -!DPFusion.map_mul //.
by rewrite (centP Cs x Px).
Qed.

End ImageControl.

Section NormalizerExtension.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.

Theorem normalizer_extension
    (hS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (P Q : {group S}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed F f -> DPFusion.image f = Q ->
  DPFusionSystem.fully_normalized F Q ->
  exists g : DPFusion.map P Q,
    DPFusionSystem.allowed F g /\ DPFusion.image g = Q /\
    exists h : DPFusion.map 'N(P)%G 'N(Q)%G,
      DPFusionSystem.allowed F h /\ {in P, h =1 g}.
Proof.
move=> hf onto hQ.
have [hCQ sylQ] := DPFusionSaturation.saturation_fully_normalized sat hQ.
have [g [hg [ontog hdom]]] :=
  DPFusionSylowAdjustment.sylow_adjust_normalizer hS hf onto sylQ.
have hex := DPFusionSaturation.saturation_extension sat hg ontog hCQ.
rewrite hdom in hex; case: hex=> h [hh hext].
have him : DPFusion.image h \subset 'N(Q).
  apply/subsetP=> y /morphimP[s Ns _ ->].
  exact: (@extension_maps_normalizer S P Q 'N(P)%G g h (normG P) ontog hext s Ns Ns).
exists g; split=> //; split=> //.
exists (DPFusion.corestrict him); split.
- exact: DPFusionSystem.corestriction_allowed him hh.
- move=> x Px; rewrite DPFusion.corestrict_in ?(subsetP (normG P)) //.
  exact: hext x Px.
Qed.

End NormalizerExtension.
End DPFusionNormalizerExtension.
