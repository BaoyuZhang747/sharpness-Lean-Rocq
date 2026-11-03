(** Actual receptivity for fusion through a faithful embedding, via a
    proved Sylow adjustment in the ambient centralizer-normalizer product. *)
From mathcomp Require Import all_boot all_fingroup pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionReceptivity.
From DiazParkV16b Require Import FiniteGroupFusionEmbedding FiniteGroupFusionEmbeddingImage
  FiniteGroupFusionEmbeddingSubgroups FiniteGroupFusionEmbeddingNormalizer FiniteGroupFusionAdjustment.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFiniteGroupFusionEmbeddingImage DPFiniteGroupFusionEmbeddingSubgroups
  DPFiniteGroupFusionEmbeddingNormalizer DPFiniteGroupFusionAdjustment.
Local Open Scope group_scope.

Module DPFiniteGroupFusionEmbeddingExtension.
Section Extension.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Hypothesis injE : 'injm E.
Local Notation T := (image_group E).
Variables P Q : {group N}.
Variable f : DPFusion.map P Q.
Variable g : G.
Hypothesis hg : {in P, forall x, E (f x) = E x ^ g}.
Hypothesis onto : DPFusion.image f = Q.

Lemma extension_displacement (s t : N) :
  s \in 'N(P) -> t \in 'N(Q) ->
  {in P, forall x, f (x ^ s) = (f x) ^ t} ->
  (E s ^ g) * (E t)^-1 \in 'C(ambient E Q).
Proof.
move=> hs ht hst; apply/centP=> y /morphimP[z _ hz ->].
have hzI : z \in DPFusion.image f by rewrite onto.
case/morphimP: hzI=> x hx _ ex.
change (z = f x) in ex; rewrite ex.
have hxs : x ^ s \in P by rewrite memJ_norm.
have he := congr1 E (hst x hx).
rewrite (morphJ E (in_setT (f x)) (in_setT t)) (hg hxs)
  (morphJ E (in_setT x) (in_setT s)) in he.
have hc : E (f x) ^ (E s ^ g) = E (f x) ^ E t.
  rewrite (hg hx).
  have hm := morphJ (conjgm [set: G]%G g) (in_setT (E x)) (in_setT (E s)).
  change ((E x ^ E s) ^ g = (E x ^ g) ^ (E s ^ g)) in hm.
  rewrite -hm -(hg hx); exact he.
apply/commgP; rewrite commg1_sym; apply/conjg_fixP.
by rewrite conjgM hc conjgK.
Qed.

Lemma extension_conjugate_sub_product :
  ambient E (DPFusionSaturation.extension_domain f) :^ g \subset
    'C(ambient E Q) * 'N_T(ambient E Q).
Proof.
apply/subsetP=> y /imsetP[z /morphimP[s _ hs ->] ->].
have /setIdP[hNs /exists_inP[t ht /forall_inP hst]] := hs.
have hc : (E s ^ g) * (E t)^-1 \in 'C(ambient E Q).
  apply: extension_displacement hNs ht _.
  move=> x hx; exact: eqP (hst x hx).
have hEt : E t \in 'N_T(ambient E Q).
  have hm := ambient_mem E ht; by rewrite ambient_normalizer in hm.
apply/mulsgP; exists ((E s ^ g) * (E t)^-1) (E t)=> //.
by rewrite mulgKV.
Qed.

Theorem extension_of_normalizer_sylow (p : nat) :
  p.-group [set: N] -> p.-Sylow('N(ambient E Q)) 'N_T(ambient E Q) ->
  exists fhat : DPFusion.map (DPFusionSaturation.extension_domain f) [set: N]%G,
    DPFusionSystem.allowed (DPFiniteGroupFusionEmbedding.system E) fhat /\ {in P, fhat =1 f}.
Proof.
move=> pN sylQ.
have pA : p.-group (ambient E (DPFusionSaturation.extension_domain f) :^ g).
  rewrite pgroupJ; exact (morphim_pgroup E (pgroupS (subsetT _) pN)).
have [c [hc hs]] := sylow_central_adjust sylQ pA extension_conjugate_sub_product.
have hr : ambient E (DPFusionSaturation.extension_domain f) :^ (g*c) \subset ambient E [set: N]%G.
  rewrite conjsgM; exact: subset_trans hs (subsetIl T 'N(ambient E Q)).
exists (conjugation_map injE hr); split; first exact: conjugation_map_allowed.
move=> x hx; apply (embedding_injective injE).
rewrite conjugation_mapE ?(subsetP (DPFusionSaturation.source_extension_domain f)) //.
rewrite conjgM -(hg hx) conjgE.
have hfx := ambient_mem E (DPFusion.map_into f hx).
by rewrite -(centP hc _ hfx) mulKg.
Qed.
End Extension.

Section Receptivity.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Hypothesis injE : 'injm E.
Variable p : nat.
Hypothesis sylE : p.-Sylow([set: G]) (image_group E).

Theorem fully_normalized_receptive (Q : {group N}) :
  DPFusionSystem.fully_normalized (DPFiniteGroupFusionEmbedding.system E) Q ->
  DPFusionReceptivity.receptive (DPFiniteGroupFusionEmbedding.system E) Q.
Proof.
move=> hQ P f /DPFiniteGroupFusionEmbedding.allowedP[g hg] onto.
exact: (extension_of_normalizer_sylow injE hg onto (sylow_carrier_pgroup injE sylE)
  (fully_normalized_normalizer_sylow injE sylE hQ)).
Qed.
End Receptivity.
End DPFiniteGroupFusionEmbeddingExtension.

Print Assumptions DPFiniteGroupFusionEmbeddingExtension.extension_of_normalizer_sylow.
Print Assumptions DPFiniteGroupFusionEmbeddingExtension.fully_normalized_receptive.
