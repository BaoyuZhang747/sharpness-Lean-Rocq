From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionSaturation
  FusionOrbit FusionCentricHomAction FusionCentricNormalizerExtension FusionCentricRigidity.
Import DPFusion DPFusionOrbit DPFusionCentricHomAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricHomRestriction.
Section Restriction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variables P N T : {group S}.
Hypothesis sPN : P \subset N.
Hypothesis sNN : N \subset 'N(P).
Hypothesis centricP : DPFusionSystem.centric F P.

Definition inclusion_arrow : DPFusionSystem.arrow F P N :=
  Sub (DPFusion.inclusion sPN) (DPFusionSystem.inclusion_allowed F sPN).
Definition restriction (f : orbit_hom F N T) : orbit_hom F P T :=
  orbit_compose (orbit_class inclusion_arrow) f.
Definition restricted_arrow (f : DPFusionSystem.arrow F N T) :=
  DPFusionSystem.arrow_compose inclusion_arrow f.

Lemma restriction_class (f : DPFusionSystem.arrow F N T) :
  restriction (orbit_class f) = orbit_class (restricted_arrow f).
Proof. exact: orbit_compose_class. Qed.

Lemma restricted_arrowE (f : DPFusionSystem.arrow F N T) :
  {in P, arrow_value (restricted_arrow f) =1 arrow_value f}.
Proof.
move=> x Px; change (DPFusion.compose (DPFusion.inclusion sPN) (val f) x = (val f) x).
by rewrite DPFusion.compose_in // DPFusion.inclusion_in.
Qed.

Lemma restriction_injective : injective restriction.
Proof.
apply: quotW=> f; apply: quotW=> g.
rewrite !restriction_class=> /orbit_class_eq_iff[t [Tt ht]].
apply/orbit_class_eq.
have normalPN : P <| N by apply/andP; split.
apply: (@DPFusionCentricRigidity.normal_inner_restrictions_inner S F p pS sat
  P N T normalPN centricP f g).
exists t; split=> // x Px.
by move: (ht x Px); rewrite !restricted_arrowE.
Qed.

Lemma restriction_fixed (f : orbit_hom F N T) :
  restriction f \in 'Fix_(normalizer_action F T sNN)([set: [subg N]]).
Proof.
move: f; apply: quotW=> f; rewrite restriction_class.
apply/(fixed_iff sNN)=> n Nn.
exists ((val f) n); split; first exact: DPFusion.map_into Nn.
move=> x Px.
have Nx := subsetP sPN x Px.
have Pxn : x ^ n \in P by rewrite memJ_norm ?(subsetP sNN _ Nn).
change (arrow_value (restricted_arrow f) (x ^ n) = (arrow_value (restricted_arrow f) x) ^ (val f) n).
rewrite !restricted_arrowE //.
exact: (morphJ (DPFusion.map_morphism (val f)) Nx Nn).
Qed.

Lemma fixed_restriction (f : orbit_hom F P T) :
  f \in 'Fix_(normalizer_action F T sNN)([set: [subg N]]) ->
  exists g : orbit_hom F N T, restriction g = f.
Proof.
move: f; apply: quotW=> f hf.
have compat := proj1 (fixed_iff sNN f) hf.
have [g [hg he]] := @DPFusionCentricNormalizerExtension.centric_normalizer_extension
  S F p sat P N T (val f) (valP f) centricP sPN sNN compat.
pose gg : DPFusionSystem.arrow F N T := Sub g hg.
exists (orbit_class gg); rewrite restriction_class.
apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Px.
change (DPFusion.compose (DPFusion.inclusion sPN) g x = (val f) x).
by rewrite DPFusion.compose_in // DPFusion.inclusion_in // he.
Qed.

Lemma fixed_card :
  #|'Fix_(normalizer_action F T sNN)([set: [subg N]])| = #|[set: orbit_hom F N T]|.
Proof.
have E : 'Fix_(normalizer_action F T sNN)([set: [subg N]]) =
    restriction @: [set: orbit_hom F N T].
  apply/setP=> f; apply/idP/imsetP.
  - move/fixed_restriction=> [g <-]; exists g=> //; by rewrite inE.
  - move=> [g _ ->]; exact: restriction_fixed.
rewrite E card_imset ?cardsT //; exact: restriction_injective.
Qed.

Lemma hom_card_mod : (#|[set: orbit_hom F P T]| %% p = #|[set: orbit_hom F N T]| %% p)%N.
Proof.
have pN : p.-group N := pgroupS (subsetT _) pS.
have pnT : p.-group [set: [subg N]].
  have h := morphim_pgroup (subg N) pN; by rewrite im_subg in h.
have acts : [acts [set: [subg N]], on [set: orbit_hom F P T] | normalizer_action F T sNN].
  apply/subsetP=> n _; rewrite /astabs !inE; apply/subsetP=> f _; by rewrite !inE.
have h := pgroup_fix_mod pnT acts.
rewrite /afix setTI fixed_card in h.
exact h.
Qed.

End Restriction.
End DPFusionCentricHomRestriction.





