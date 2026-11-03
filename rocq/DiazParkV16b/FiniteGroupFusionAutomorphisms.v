(** The actual ambient normalizer action realizes the full fusion automizer. *)
From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionAutomorphisms FusionCentralizerMaps.
From DiazParkV16b Require Import FiniteGroupFusion FiniteGroupFusionSubgroups
  FiniteGroupFusionNormalizer.
Import DPFusion DPFusionSubgroup DPFusionAutomorphisms
  DPFiniteGroupFusion DPFiniteGroupFusionSubgroups DPFiniteGroupFusionNormalizer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFiniteGroupFusionAutomorphisms.
Section Action.
Variable G : finGroupType.
Variable T : {group G}.
Local Notation S := [subg T]%type.
Variable P : {group S}.

Lemma normalizer_conjugation_sub (g : [subg 'N(ambient P)%G]%type) :
  ambient P :^ val g \subset ambient P.
Proof. by rewrite (normP (subgP g)). Qed.

Definition normalizer_element_action (g : [subg 'N(ambient P)%G]%type) : {perm S} :=
  map_aut (DPFiniteGroupFusion.conjugation_map (normalizer_conjugation_sub g)).

Definition normalizer_action (g : G) : {perm S} :=
  normalizer_element_action (subg 'N(ambient P)%G g).

Lemma normalizer_action_allowed (g : G) :
  normalizer_action g \in DPFusionSaturation.aut_group (DPFiniteGroupFusion.system T) P.
Proof.
rewrite /normalizer_action /normalizer_element_action.
apply: (@map_aut_allowed _ (DPFiniteGroupFusion.system T) P).
exact: DPFiniteGroupFusion.conjugation_map_allowed.
Qed.

Lemma normalizer_action_mem (g : G) : normalizer_action g \in Aut P.
Proof.
exact: subsetP (DPFusionSaturation.aut_group_sub (DPFiniteGroupFusion.system T) P)
  _ (normalizer_action_allowed g).
Qed.

Lemma normalizer_actionE g x :
  g \in 'N(ambient P) -> x \in P -> val (normalizer_action g x) = (val x) ^ g.
Proof.
move=> Ng Px; rewrite /normalizer_action /normalizer_element_action.
by rewrite map_autE // DPFiniteGroupFusion.conjugation_mapE // subgK.
Qed.

Lemma normalizer_action_morphic :
  {in 'N(ambient P) &, {morph normalizer_action : g h / g * h}}.
Proof.
move=> g h Ng Nh.
apply: (eq_Aut (normalizer_action_mem _) (groupM (normalizer_action_mem _) (normalizer_action_mem _)))=> x Px.
apply: val_inj; rewrite permM (normalizer_actionE (groupM Ng Nh) Px).
rewrite (normalizer_actionE Nh (Aut_closed (normalizer_action_mem g) Px)).
by rewrite (normalizer_actionE Ng Px) conjgM.
Qed.

Canonical normalizer_morphism := Morphism normalizer_action_morphic.

Lemma normalizer_image :
  normalizer_morphism @* 'N(ambient P) =
    DPFusionSaturation.aut_group (DPFiniteGroupFusion.system T) P.
Proof.
apply/setP=> a; apply/idP/idP.
- move=> /morphimP[g Ng _ ->]; exact: normalizer_action_allowed.
- move=> /setIdP[Aa /existsP[f /andP[/DPFiniteGroupFusion.allowedP[g hg] /forall_inP hf]]].
  have Ng : g \in 'N(ambient P).
    apply/normP; by rewrite (ambient_conjugation_image hg) endomorphism_image.
  apply/morphimP; exists g=> //.
  apply: (eq_Aut Aa (normalizer_action_mem g))=> x Px; apply: val_inj.
  rewrite normalizer_actionE // -(eqP (hf x Px)); exact: hg.
Qed.

Lemma normalizer_action_subgroup (g : S) :
  g \in 'N(P) -> normalizer_action (val g) = conj_aut P g.
Proof.
move=> Ng.
have Nvg : val g \in 'N(ambient P).
  have h := ambient_mem Ng; rewrite ambient_normalizer in h; exact: (setIP h).2.
apply: (eq_Aut (normalizer_action_mem _) (Aut_aut _ _))=> x Px; apply: val_inj.
by rewrite normalizer_actionE // norm_conj_autE.
Qed.

Lemma subgroup_normalizer_image :
  normalizer_morphism @* 'N_T(ambient P) = DPFusionSaturation.ambient_aut_group P.
Proof.
apply/setP=> a; apply/idP/idP.
- move=> /morphimP[g _ Ng ->].
  have Ng' : g \in ambient 'N(P)%G by rewrite ambient_normalizer.
  have Nsg := ambient_repr Ng'.
  have eg := ambient_subgK Ng'.
  change (normalizer_action g \in conj_aut P @* 'N(P)).
  rewrite -eg (normalizer_action_subgroup Nsg).
  exact (mem_morphim (conj_aut P) Nsg Nsg).
- move=> /morphimP[g Ng _ ->].
  have Nvg : val g \in 'N_T(ambient P).
    have hmem := ambient_mem Ng; by rewrite ambient_normalizer in hmem.
  apply/morphimP; exists (val g)=> //; first exact: (setIP Nvg).2.
  exact: esym (normalizer_action_subgroup Ng).
Qed.

Theorem fully_normalized_automizer_sylow (p : nat)
    (sylT : p.-Sylow([set: G]) T) :
  DPFusionSystem.fully_normalized (DPFiniteGroupFusion.system T) P ->
  p.-Sylow(DPFusionSaturation.aut_group (DPFiniteGroupFusion.system T) P)
    (DPFusionSaturation.ambient_aut_group P).
Proof.
move=> hP.
have hs := fully_normalized_normalizer_sylow sylT hP.
have him := morphim_pHall normalizer_morphism (subsetIr T 'N(ambient P)) hs.
by rewrite normalizer_image subgroup_normalizer_image in him.
Qed.

End Action.
End DPFiniteGroupFusionAutomorphisms.

Print Assumptions DPFiniteGroupFusionAutomorphisms.normalizer_image.
Print Assumptions DPFiniteGroupFusionAutomorphisms.fully_normalized_automizer_sylow.
