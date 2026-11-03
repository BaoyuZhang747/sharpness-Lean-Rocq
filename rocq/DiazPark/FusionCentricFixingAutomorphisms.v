From mathcomp Require Import all_ssreflect all_fingroup center pgroup sylow.
From DiazPark Require Import GroupInfrastructure FusionMaps FusionSystems FusionSaturation
  FusionConjugacy FusionAutomorphisms FusionSylowAdjustment FusionCentricCriterion FusionCentricBasics.
Import DPFusion DPFusionAutomorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentricFixing.
Section FixingGroup.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables U V : {group S}.

Definition fixing_set := [set a in DPFusionSaturation.aut_group F V |
  [forall x in U, a x == x]].

Lemma fixing_group_set : group_set fixing_set.
Proof.
apply/group_setP; split.
- apply/setIdP; split; first exact: group1.
  by apply/forall_inP=> x Ux; rewrite perm1.
- move=> a b /setIdP[Fa /forall_inP ha] /setIdP[Fb /forall_inP hb].
  apply/setIdP; split; first exact: groupM Fa Fb.
  by apply/forall_inP=> x Ux; rewrite permM (eqP (ha x Ux)) (eqP (hb x Ux)).
Qed.
Definition fixing_group : {group {perm S}} := group fixing_group_set.
Lemma fixing_sub : fixing_group \subset DPFusionSaturation.aut_group F V.
Proof. by apply/subsetP=> a /setIdP[Fa _]. Qed.
Lemma fixing_pointwise a : a \in fixing_group -> {in U, a =1 id}.
Proof. move=> /setIdP[_ /forall_inP h] x Ux; exact: eqP (h x Ux). Qed.

Hypothesis normalUV : U <| V.
Hypothesis centricU : DPFusionSystem.centric F U.

Lemma fixing_displacement a : a \in fixing_group ->
  forall x, x \in V -> x^-1 * a x \in U.
Proof.
move=> ha x Vx.
have Aa : a \in Aut V := subsetP (DPFusionSaturation.aut_group_sub F V) a (subsetP fixing_sub a ha).
have hfix := fixing_pointwise ha.
have sUV := normal_sub normalUV.
have Nx : x \in 'N(U) := subsetP (normal_norm normalUV) x Vx.
have hconj : {in U, forall u, u ^ (a x) = u ^ x}.
  move=> u Uu.
  have Uux : u ^ x \in U by rewrite memJ_norm.
  have hm := morphJ (autm Aa) (subsetP sUV u Uu) Vx.
  change (a (u ^ x) = (a u) ^ (a x)) in hm.
  by rewrite (hfix _ Uux) (hfix _ Uu) in hm; symmetry.
have hcent : x^-1 * a x \in 'C(U).
  apply/centP=> u Uu; apply/commgP; rewrite commg1_sym; apply/conjg_fixP.
  have Uux : u ^ x^-1 \in U by rewrite memJ_norm ?groupV.
  by rewrite conjgM (hconj _ Uux) conjgKV.
exact: subsetP (DPFusionCentricCriterion.centric_self_centralizing centricU) _ hcent.
Qed.

Lemma fixing_pgroup (p : nat) : p.-group U -> p.-group fixing_group.
Proof.
move=> pU; apply: (@automorphism_displacement_pgroup S V U fixing_group _
  (normal_sub normalUV) _ _ p pU).
- exact: subset_trans fixing_sub (DPFusionSaturation.aut_group_sub F V).
- exact: fixing_pointwise.
- exact: fixing_displacement.
Qed.

Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.

Theorem fixing_inner a : a \in fixing_group ->
  exists z, z \in 'Z(U) /\ {in V, forall x, a x = x ^ z}.
Proof.
move=> ha.
have sUV := normal_sub normalUV.
have [W [/existsP[f /andP[hf /eqP onto]] hW]] :=
  DPFusionConjugacy.fully_normalized_conjugate_exists F V.
have [_ sylW] := DPFusionSaturation.saturation_fully_normalized sat hW.
have pU := pgroupS (subsetT U) pS.
have [g [hg [ontog htransport]]] := DPFusionSylowAdjustment.sylow_adjust_transport
  hf onto fixing_sub (fixing_pgroup pU) sylW.
have Aa : a \in Aut V := subsetP (DPFusionSaturation.aut_group_sub F V) a (subsetP fixing_sub a ha).
have ta : aut_transport g a \in aut_transport_group g fixing_group.
  by apply/morphimP; exists a.
have /morphimP[s Ns _ hs] := subsetP htransport _ ta.
pose gr := DPFusion.restrict g sUV.
have cI := DPFusionCentricBasics.centric_image (DPFusionSystem.restriction_allowed sUV hg) centricU.
have Cs : s \in 'C(DPFusion.image gr).
  apply/centP=> y /morphimP[u Uu _ hy]; apply/commgP; rewrite commg1_sym; apply/conjg_fixP.
  change (y = gr u) in hy; rewrite hy /gr DPFusion.restrict_in //.
  have Vu := subsetP sUV u Uu.
  have h := congr1 (fun b : {perm S} => b (g u)) hs.
  rewrite norm_conj_autE ?DPFusion.map_into // in h.
  by rewrite (aut_transportE g Aa Vu) (fixing_pointwise ha Uu) in h.
have Is := subsetP (DPFusionCentricCriterion.centric_self_centralizing cI) s Cs.
have /morphimP[z Uz _ hz] := Is.
change (s = gr z) in hz.
have hz' : s = g z by rewrite hz /gr DPFusion.restrict_in.
have conjugates : {in V, forall x, a x = x ^ z}.
  move=> x Vx.
  have Vz := subsetP sUV z Uz.
  have h := congr1 (fun b : {perm S} => b (g x)) hs.
  rewrite norm_conj_autE ?DPFusion.map_into // in h.
  rewrite (aut_transportE g Aa Vx) hz' -(morphJ (DPFusion.map_morphism g) Vx Vz) in h.
  exact: DPFusion.map_injective (Aut_closed Aa Vx) (groupJ Vx Vz) h.
exists z; split=> //; apply/setIP; split=> //; apply/centP=> u Uu.
apply/commgP; rewrite commg1_sym; apply/conjg_fixP.
by rewrite -(conjugates u (subsetP sUV u Uu)) (fixing_pointwise ha Uu).
Qed.

End FixingGroup.
End DPFusionCentricFixing.
