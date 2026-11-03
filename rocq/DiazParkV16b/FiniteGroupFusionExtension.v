(** Actual extension-domain conjugation into a centralizer-normalizer product,
    followed by an actual centralizer adjustment of the original conjugator. *)
From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionCentralizerMaps FusionReceptivity.
From DiazParkV16b Require Import FiniteGroupFusion FiniteGroupFusionSubgroups
  FiniteGroupFusionNormalizer FiniteGroupFusionAdjustment.
Import DPFusion DPFusionSubgroup DPFiniteGroupFusion DPFiniteGroupFusionSubgroups
  DPFiniteGroupFusionNormalizer DPFiniteGroupFusionAdjustment.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFiniteGroupFusionExtension.
Section Extension.
Variable G : finGroupType.
Variable T : {group G}.
Local Notation S := [subg T]%type.
Variables P Q : {group S}.
Variable f : DPFusion.map P Q.
Variable g : G.
Hypothesis hg : {in P, forall x, val (f x) = (val x) ^ g}.
Hypothesis onto : DPFusion.image f = Q.

Lemma extension_displacement (s t : S) :
  s \in 'N(P) -> t \in 'N(Q) ->
  {in P, forall x, f (x ^ s) = (f x) ^ t} ->
  ((val s) ^ g) * (val t)^-1 \in 'C(ambient Q).
Proof.
move=> Ns Nt hst; apply/centP=> y /morphimP[z _ Qz ->].
have Iz : z \in DPFusion.image f by rewrite onto.
case/morphimP: Iz=> x Px _ ez.
change (z = f x) in ez; rewrite ez.
have Pxs : x ^ s \in P by rewrite memJ_norm.
have he := congr1 (fun u : S => val u) (hst x Px).
change (val (f (x ^ s)) = (val (f x)) ^ val t) in he.
rewrite (hg Pxs) in he.
change (((val x) ^ val s) ^ g = (val (f x)) ^ val t) in he.
have hc : (val (f x)) ^ ((val s) ^ g) = (val (f x)) ^ val t.
  rewrite (hg Px).
  have xG : val x \in [set: G] by rewrite inE.
  have sG : val s \in [set: G] by rewrite inE.
  have hm := morphJ (conjgm [set: G]%G g) xG sG.
  change (((val x) ^ val s) ^ g = ((val x) ^ g) ^ ((val s) ^ g)) in hm.
  rewrite -hm -(hg Px); exact: he.
apply/commgP; rewrite commg1_sym; apply/conjg_fixP.
by rewrite conjgM hc conjgK.
Qed.

Lemma extension_conjugate_sub_product :
  ambient (DPFusionSaturation.extension_domain f) :^ g \subset
    'C(ambient Q) * 'N_T(ambient Q).
Proof.
apply/subsetP=> y /imsetP[z /morphimP[s _ Es ->] ->].
have /setIdP[Ns /exists_inP[t Nt /forall_inP hst]] := Es.
have hc : ((val s) ^ g) * (val t)^-1 \in 'C(ambient Q).
  apply: extension_displacement Ns Nt _.
  move=> x Px; exact: eqP (hst x Px).
have ht : val t \in 'N_T(ambient Q).
  have hm := ambient_mem Nt; by rewrite ambient_normalizer in hm.
apply/mulsgP; exists (((val s) ^ g) * (val t)^-1) (val t)=> //.
by rewrite mulgKV.
Qed.

Theorem extension_of_normalizer_sylow (p : nat) :
  p.-group [set: S] -> p.-Sylow('N(ambient Q)) 'N_T(ambient Q) ->
  exists fhat : DPFusion.map (DPFusionSaturation.extension_domain f) [set: S]%G,
    DPFusionSystem.allowed (DPFiniteGroupFusion.system T) fhat /\ {in P, fhat =1 f}.
Proof.
move=> pS sylQ.
have pE : p.-group (ambient (DPFusionSaturation.extension_domain f) :^ g).
  rewrite pgroupJ.
  change (p.-group (sgval @* DPFusionSaturation.extension_domain f)).
  exact: (morphim_pgroup sgval (pgroupS (subsetT _) pS)).
have [c [Cc sEc]] := sylow_central_adjust sylQ pE extension_conjugate_sub_product.
have htarget : ambient (DPFusionSaturation.extension_domain f) :^ (g * c) \subset
    ambient [set: S]%G.
  rewrite ambient_top conjsgM.
  exact: subset_trans sEc (subsetIl T 'N(ambient Q)).
exists (DPFiniteGroupFusion.conjugation_map htarget); split.
- exact: DPFiniteGroupFusion.conjugation_map_allowed.
- move=> x Px; apply: val_inj.
  rewrite DPFiniteGroupFusion.conjugation_mapE ?(subsetP (DPFusionSaturation.source_extension_domain f)) //.
  rewrite conjgM -(hg Px) conjgE.
  have Qfx := ambient_mem (DPFusion.map_into f Px).
  by rewrite -(centP Cc _ Qfx) mulKg.
Qed.

End Extension.

Section Receptivity.
Variable G : finGroupType.
Variable T : {group G}.
Local Notation S := [subg T]%type.
Variable p : nat.
Hypothesis sylT : p.-Sylow([set: G]) T.

Theorem fully_normalized_receptive (Q : {group S}) :
  DPFusionSystem.fully_normalized (DPFiniteGroupFusion.system T) Q ->
  DPFusionReceptivity.receptive (DPFiniteGroupFusion.system T) Q.
Proof.
move=> hQ P f /DPFiniteGroupFusion.allowedP[g hg] onto.
exact: (extension_of_normalizer_sylow hg onto (sylow_carrier_pgroup sylT)
  (fully_normalized_normalizer_sylow sylT hQ)).
Qed.

End Receptivity.
End DPFiniteGroupFusionExtension.

Print Assumptions DPFiniteGroupFusionExtension.extension_of_normalizer_sylow.
Print Assumptions DPFiniteGroupFusionExtension.fully_normalized_receptive.
