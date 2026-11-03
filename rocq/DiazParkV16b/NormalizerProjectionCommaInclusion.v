(** The literal fixed-chain category includes into the actual projection
    comma category. The triangle is proved using the actual thin index category. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryComma CategoryIsomorphism FusionSystems.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndexCategory
  NormalizerOrbitPairCategory NormalizerOrbitPairProjection NormalizerOrbitSameChainCategory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChainIndex.

Module DPNormalizerProjectionCommaInclusion.
Section Inclusion.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable c : chain F.
Variable d : index_object F.
Variable hc : chain_class c = d.
Local Notation p := (DPNormalizerOrbitPairProjection.projection F).
Local Notation D := (DPNormalizerOrbitSameChain.category c).
Local Notation C := (costructured_category p d).

Definition object (P : D) : C.
Proof.
refine (@Build_costructured_object _ _ p d (DPNormalizerOrbitSameChain.point P) _).
apply: hom_of_relation.
change (is_true (index_relation (chain_class c) d)).
rewrite hc; exact: index_relation_refl.
Defined.

Definition to_comma_arrow (X : C) (P : D)
    (u : DPNormalizerOrbitPair.pair_hom (costructured_source X) (DPNormalizerOrbitSameChain.point P)) :
    hom C X (object P).
Proof.
refine (@Build_costructured_hom _ _ p d X (object P) u _).
exact: index_hom_unique.
Defined.

Definition inclusion : functor D C.
Proof.
refine (@Build_functor D C object (fun P Q f => @to_comma_arrow (object P) Q f) _ _).
- move=> P; apply costructured_hom_ext; reflexivity.
- move=> P Q T f g; apply costructured_hom_ext; reflexivity.
Defined.

Lemma inclusion_full (P Q : D) (f : hom C (object P) (object Q)) :
  exists g : hom D P Q, fmap inclusion g = f.
Proof.
exists (costructured_map f); apply costructured_hom_ext; reflexivity.
Qed.

Lemma inclusion_faithful (P Q : D) : injective (@fmap _ _ inclusion P Q).
Proof. move=> f g h; exact (congr1 costructured_map h). Qed.

Lemma inclusion_projection :
  functor_comp inclusion (costructured_projection p d) = DPNormalizerOrbitSameChain.inclusion c.
Proof.
apply (@functor_extensionality D (DPNormalizerOrbitPair.pair_category F)
  (functor_comp inclusion (costructured_projection p d))
  (DPNormalizerOrbitSameChain.inclusion c) (Logic.eq_refl _)); reflexivity.
Qed.
End Inclusion.
End DPNormalizerProjectionCommaInclusion.
