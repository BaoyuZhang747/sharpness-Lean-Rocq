(** Literal inverse categories between the ambient-centric local collection
    and the fixed-chain part of the actual global pair category. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryReindex CategoryIsomorphism
  FusionSystems FusionSaturation FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects
  ChainNormalizerFusionOrbit NormalizerOrbitSameChainCategory NormalizerOrbitSameChainCollection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPChainNormalizerFusionOrbit DPNormalizerOrbitSameChainCollection.

Module DPNormalizerOrbitSameChainEquivalence.
Section Equivalence.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.
Local Notation X := (collection_category L c).
Local Notation Y := (DPNormalizerOrbitSameChain.category c).
Local Notation J := (@to_same S F L c p sat).

Definition same_reindexed : category := reindexed_category Y (@to_same_object S F L c).

Definition forward_reindexed : functor X same_reindexed.
Proof.
refine (@Build_functor X same_reindexed (fun P => P) (fun P Q f => fmap J f) _ _).
- move=> P; exact (fmap_id J P).
- move=> P Q U f g; exact (fmap_compose J f g).
Defined.

Definition backward_map (P Q : X) (f : hom same_reindexed P Q) : hom X P Q :=
  proj1_sig (cid (@to_same_full S F L c p sat P Q f)).

Lemma backward_map_spec (P Q : X) (f : hom same_reindexed P Q) :
  fmap J (backward_map f) = f.
Proof. exact: proj2_sig (cid (@to_same_full S F L c p sat P Q f)). Qed.

Lemma backward_forward_map (P Q : X) (f : hom X P Q) :
  backward_map (fmap J f) = f.
Proof. apply: (@to_same_faithful S F L c p sat P Q); exact: backward_map_spec. Qed.

Definition backward_reindexed : functor same_reindexed X.
Proof.
refine (@Build_functor same_reindexed X (fun P => P) backward_map _ _).
- move=> P; apply: (@to_same_faithful S F L c p sat P P).
  rewrite backward_map_spec; exact: esym (fmap_id J P).
- move=> P Q U f g; apply: (@to_same_faithful S F L c p sat P U).
  rewrite backward_map_spec fmap_compose !backward_map_spec; reflexivity.
Defined.

Definition reindexed_isomorphism : category_isomorphism X same_reindexed.
Proof.
refine (@Build_category_isomorphism X same_reindexed forward_reindexed backward_reindexed _ _).
- apply: (@functor_ext_pointwise X X
    (functor_comp forward_reindexed backward_reindexed) (functor_id X)
    (fun P => Logic.eq_refl P)).
  move=> P Q f; rewrite hom_transport_loop; exact: backward_forward_map.
- apply: (@functor_ext_pointwise same_reindexed same_reindexed
    (functor_comp backward_reindexed forward_reindexed) (functor_id same_reindexed)
    (fun P => Logic.eq_refl P)).
  move=> P Q f; rewrite hom_transport_loop; exact: backward_map_spec.
Defined.

Definition collection_isomorphism : category_isomorphism X Y :=
  category_iso_trans reindexed_isomorphism
    (@reindex_category_isomorphism Y X (@to_same_object S F L c)
      (@from_same_object S F L c) (@same_object_roundtrip S F L c)
      (@collection_object_roundtrip S F L c)).

Lemma collection_forward : category_iso_forward collection_isomorphism = J.
Proof.
apply (@functor_ext_pointwise X Y (category_iso_forward collection_isomorphism) J
  (fun P => Logic.eq_refl (@to_same_object S F L c P))).
move=> P Q f; rewrite hom_transport_loop; reflexivity.
Qed.

Lemma collection_forward_forget :
  functor_comp (category_iso_forward collection_isomorphism)
    (DPNormalizerOrbitSameChain.forget c) =
  @collection_ambient_functor S F L c p sat.
Proof.
rewrite collection_forward.
apply (@functor_ext_pointwise X (DPFusionOrbit.centric_orbit_category F)
  (functor_comp J (DPNormalizerOrbitSameChain.forget c))
  (@collection_ambient_functor S F L c p sat)
  (fun P => Logic.eq_refl (@collection_ambient_object S F c P))).
move=> P Q f; rewrite hom_transport_loop; reflexivity.
Qed.

End Equivalence.
End DPNormalizerOrbitSameChainEquivalence.
