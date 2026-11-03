From mathcomp Require Import all_ssreflect all_fingroup generic_quotient center pgroup nilpotent.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionSaturation
  FusionAutomorphisms FusionCentricBasics FusionCentricCriterion FusionCentricFixingAutomorphisms.
Import DPFusion DPFusionOrbit DPFusionAutomorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricRigidity.
Section NormalRigidity.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables U V T : {group S}.
Hypothesis normalUV : U <| V.
Hypothesis centricU : DPFusionSystem.centric F U.
Variables f g : DPFusion.map V T.
Hypothesis f_allowed : DPFusionSystem.allowed F f.
Hypothesis sameU : {in U, f =1 g}.

Lemma equal_on_normal_centric_image_sub : DPFusion.image g \subset DPFusion.image f.
Proof.
have sUV := normal_sub normalUV.
pose fr := DPFusion.restrict f sUV.
have cL := DPFusionCentricBasics.centric_image
  (DPFusionSystem.restriction_allowed sUV f_allowed) centricU.
have sLf : DPFusion.image fr \subset DPFusion.image f.
  apply/subsetP=> y /morphimP[u Uu _ hy].
  change (y = fr u) in hy; rewrite hy /fr DPFusion.restrict_in //.
    exact (@DPFusion.image_mem S V T f u (subsetP sUV u Uu)).
apply/subsetP=> y /morphimP[x Vx _ hy].
change (y = g x) in hy; rewrite hy.
have Nx : x \in 'N(U) := subsetP (normal_norm normalUV) x Vx.
have hc : g x * (f x)^-1 \in 'C(DPFusion.image fr).
  apply/centP=> z /morphimP[u Uu _ hz]; apply/commgP; rewrite commg1_sym; apply/conjg_fixP.
  change (z = fr u) in hz; rewrite hz /fr DPFusion.restrict_in // conjgM.
  have Vu := subsetP sUV u Uu.
  have Uux : u ^ x \in U by rewrite memJ_norm.
  have hf : f (u ^ x) = (f u) ^ (f x) := morphJ (DPFusion.map_morphism f) Vu Vx.
  have hg : g (u ^ x) = (g u) ^ (g x) := morphJ (DPFusion.map_morphism g) Vu Vx.
  rewrite -(@sameU _ Uux) -(@sameU _ Uu) hf in hg.
  by rewrite -hg conjgK.
have hratio := subsetP sLf _ (subsetP (DPFusionCentricCriterion.centric_self_centralizing cL) _ hc).
have h := groupM hratio (DPFusion.image_mem f Vx).
by rewrite mulgKV in h.
Qed.

End NormalRigidity.

Section SaturatedNormalRigidity.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variables U V T : {group S}.
Hypothesis normalUV : U <| V.
Hypothesis centricU : DPFusionSystem.centric F U.
Variables f g : DPFusionSystem.arrow F V T.

Lemma normal_equal_restrictions_inner :
  {in U, arrow_value f =1 arrow_value g} -> target_inner f g.
Proof.
move=> heq; rewrite /arrow_value in heq.
have imsub := equal_on_normal_centric_image_sub normalUV centricU (valP f) heq.
pose gg := DPFusion.corestrict imsub.
pose a := DPFusion.compose gg (DPFusion.inverse (val f)).
have ha : DPFusionSystem.allowed F a.
  apply: DPFusionSystem.composition_closed; last exact: DPFusionSystem.inverse_closed (valP f).
  exact: DPFusionSystem.corestriction_allowed imsub (valP g).
have fixa : map_aut a \in DPFusionCentricFixing.fixing_group F U V.
  apply/setIdP; split; first exact: map_aut_allowed ha.
  apply/forall_inP=> u Uu; apply/eqP.
  have Vu := subsetP (normal_sub normalUV) u Uu.
  rewrite map_autE // /a DPFusion.compose_in // /gg DPFusion.corestrict_in //.
  rewrite -(heq u Uu); exact: DPFusion.inverse_cancel Vu.
have [z [Zz hz]] := DPFusionCentricFixing.fixing_inner normalUV centricU pS sat fixa.
have Uz := subsetP (center_sub U) z Zz.
have Vz := subsetP (normal_sub normalUV) z Uz.
apply/exists_inP; exists ((val f) z); first exact: DPFusion.map_into Vz.
apply/forall_inP=> x Vx; apply/eqP.
have eqx : a x = x ^ z by rewrite -(map_autE a Vx); exact: hz x Vx.
have gf : (val f) (a x) = (val g) x.
  rewrite /a DPFusion.compose_in // /gg DPFusion.corestrict_in //.
  apply: DPFusion.inverse_cancel_right; exact: subsetP imsub _ (DPFusion.image_mem (val g) Vx).
rewrite /arrow_value -gf eqx.
exact (morphJ (DPFusion.map_morphism (val f)) Vx Vz).
Qed.

End SaturatedNormalRigidity.

Section SaturatedNormalInnerRigidity.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variables U V T : {group S}.
Hypothesis normalUV : U <| V.
Hypothesis centricU : DPFusionSystem.centric F U.
Variables f g : DPFusionSystem.arrow F V T.

Lemma normal_inner_restrictions_inner :
  (exists t, t \in T /\ {in U, forall u, arrow_value g u = (arrow_value f u) ^ t}) ->
  target_inner f g.
Proof.
move=> [t [Tt ht]].
have nTt : t \in 'N(T) := subsetP (normG T) t Tt.
have sTT : T :^ t \subset T by rewrite (normP nTt).
pose c : DPFusionSystem.arrow F T T := Sub (DPFusion.conjugation sTT) (DPFusionSystem.conjugation_closed F sTT).
pose ft := DPFusionSystem.arrow_compose f c.
have eqU : {in U, arrow_value ft =1 arrow_value g}.
  move=> u Uu; have Vu := subsetP (normal_sub normalUV) u Uu.
  rewrite /ft /arrow_value /DPFusionSystem.arrow_compose /= DPFusion.compose_in //.
  rewrite DPFusion.conjugation_in ?DPFusion.map_into //; exact: esym (ht u Uu).
have innerfg := @normal_equal_restrictions_inner S F p pS sat U V T normalUV centricU ft g eqU.
apply: target_inner_trans innerfg.
apply/exists_inP; exists t=> //; apply/forall_inP=> x Vx.
by rewrite /ft /arrow_value /DPFusionSystem.arrow_compose /= DPFusion.compose_in // DPFusion.conjugation_in ?DPFusion.map_into.
Qed.

End SaturatedNormalInnerRigidity.
End DPFusionCentricRigidity.
