(** The actual ambient normalizer realizes the automizer of fusion
    through a faithful finite-group embedding. *)
From mathcomp Require Import all_boot all_fingroup pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionAutomorphisms.
From DiazParkV16b Require Import FiniteGroupFusionEmbedding FiniteGroupFusionEmbeddingImage
  FiniteGroupFusionEmbeddingSubgroups FiniteGroupFusionEmbeddingNormalizer.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionAutomorphisms DPFiniteGroupFusionEmbeddingImage
  DPFiniteGroupFusionEmbeddingSubgroups DPFiniteGroupFusionEmbeddingNormalizer.
Local Open Scope group_scope.

Module DPFiniteGroupFusionEmbeddingAutomorphisms.
Section Automorphisms.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Hypothesis injE : 'injm E.
Variable P : {group N}.
Local Notation T := (image_group E).
Local Notation AP := (ambient E P).

Lemma normalizer_conjugation_sub (g : [subg 'N(AP)%G]) : AP :^ val g \subset AP.
Proof. by rewrite (normP (valP g)). Qed.

Definition normalizer_element_action (g : [subg 'N(AP)%G]) : {perm N} :=
  map_aut (conjugation_map injE (normalizer_conjugation_sub g)).
Definition normalizer_action (g : G) : {perm N} :=
  normalizer_element_action (subg 'N(AP)%G g).

Lemma normalizer_action_allowed (g : G) :
  normalizer_action g \in DPFusionSaturation.aut_group (DPFiniteGroupFusionEmbedding.system E) P.
Proof.
rewrite /normalizer_action /normalizer_element_action.
apply: (@map_aut_allowed _ (DPFiniteGroupFusionEmbedding.system E) P).
exact: conjugation_map_allowed.
Qed.

Lemma normalizer_action_mem (g : G) : normalizer_action g \in Aut P.
Proof.
exact: subsetP (DPFusionSaturation.aut_group_sub (DPFiniteGroupFusionEmbedding.system E) P)
  _ (normalizer_action_allowed g).
Qed.

Lemma normalizer_actionE g x : g \in 'N(AP) -> x \in P ->
  E (normalizer_action g x) = E x ^ g.
Proof.
move=> hg hx; rewrite /normalizer_action /normalizer_element_action.
by rewrite map_autE // conjugation_mapE // subgK.
Qed.

Lemma normalizer_action_morphic :
  {in 'N(AP) &, {morph normalizer_action : g h / g*h}}.
Proof.
move=> g h hg hh.
apply: (eq_Aut (normalizer_action_mem _) (groupM (normalizer_action_mem _) (normalizer_action_mem _)))=> x hx.
apply (embedding_injective injE); rewrite permM (normalizer_actionE (groupM hg hh) hx).
rewrite (normalizer_actionE hh (Aut_closed (normalizer_action_mem g) hx)).
by rewrite (normalizer_actionE hg hx) conjgM.
Qed.

Canonical normalizer_morphism := Morphism normalizer_action_morphic.

Lemma normalizer_image : normalizer_morphism @* 'N(AP) =
  DPFusionSaturation.aut_group (DPFiniteGroupFusionEmbedding.system E) P.
Proof.
apply/setP=> a; apply/idP/idP.
- move=> /morphimP[g hg _ ->]; exact: normalizer_action_allowed.
- move=> /setIdP[aa /existsP[f /andP[/DPFiniteGroupFusionEmbedding.allowedP[g hg] /forall_inP hf]]].
  have ng : g \in 'N(AP).
    apply/normP; by rewrite (ambient_conjugation_image injE hg) endomorphism_image.
  apply/morphimP; exists g=> //.
  apply: (eq_Aut aa (normalizer_action_mem g))=> x hx; apply (embedding_injective injE).
  rewrite normalizer_actionE // -(eqP (hf x hx)); exact: hg.
Qed.

Lemma normalizer_action_subgroup (g : N) : g \in 'N(P) -> normalizer_action (E g) = conj_aut P g.
Proof.
move=> hg.
have ng : E g \in 'N(AP).
  have h := ambient_mem E hg; rewrite ambient_normalizer // in h; exact: (setIP h).2.
apply: (eq_Aut (normalizer_action_mem _) (Aut_aut _ _))=> x hx.
apply (embedding_injective injE).
by rewrite normalizer_actionE // norm_conj_autE // morphJ ?inE.
Qed.

Lemma subgroup_normalizer_image :
  normalizer_morphism @* 'N_T(AP) = DPFusionSaturation.ambient_aut_group P.
Proof.
apply/setP=> a; apply/idP/idP.
- move=> /morphimP[g _ hg ->].
  have hg' : g \in ambient E 'N(P)%G by rewrite ambient_normalizer.
  have hr := ambient_repr injE hg'.
  have he := ambient_inverseK injE hg'.
  change (normalizer_action g \in conj_aut P @* 'N(P)).
  rewrite -he (normalizer_action_subgroup hr).
  exact (mem_morphim (conj_aut P) hr hr).
- move=> /morphimP[g hg _ ->].
  have hEg : E g \in 'N_T(AP).
    have hh := ambient_mem E hg; by rewrite ambient_normalizer in hh.
  apply/morphimP; exists (E g)=> //; first exact: (setIP hEg).2.
  exact: esym (normalizer_action_subgroup hg).
Qed.

Theorem fully_normalized_automizer_sylow p (sylE : p.-Sylow([set: G]) T) :
  DPFusionSystem.fully_normalized (DPFiniteGroupFusionEmbedding.system E) P ->
  p.-Sylow(DPFusionSaturation.aut_group (DPFiniteGroupFusionEmbedding.system E) P)
    (DPFusionSaturation.ambient_aut_group P).
Proof.
move=> hP; have hs := fully_normalized_normalizer_sylow injE sylE hP.
have hi := morphim_pHall normalizer_morphism (subsetIr T 'N(AP)) hs.
by rewrite normalizer_image subgroup_normalizer_image in hi.
Qed.
End Automorphisms.
End DPFiniteGroupFusionEmbeddingAutomorphisms.

Print Assumptions DPFiniteGroupFusionEmbeddingAutomorphisms.normalizer_image.
Print Assumptions DPFiniteGroupFusionEmbeddingAutomorphisms.fully_normalized_automizer_sylow.
