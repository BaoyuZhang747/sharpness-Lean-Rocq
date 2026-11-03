(** Exact kernel and order of the ordinary linking automorphism
    projection.  The kernel is the distinguished image of Z(P);
    no assertion that this image is central in Aut_L(P) is made. *)
From mathcomp Require Import all_boot all_fingroup center quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import LinkingSystem LinkingSystemAutomorphisms
  LinkingSystemFactorization LinkingSystemAutomorphismProjection.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingAutomorphisms DPLinkingFactorization DPLinkingAutomorphismProjection.
Local Open Scope group_scope.

Module DPLinkingAutomorphismKernel.
Section Kernel.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable P : DPFusionOrbit.centric_object F.
Local Notation G := (automorphism_group L P).
Local Notation AF := (DPFusionSaturation.aut_group F (val P)).
Local Notation H := [subg AF]%type.
Local Notation Z := [subg 'Z(val P)]%type.
Local Notation pr := (DPLinkingAutomorphismProjection.projection L P).

Lemma center_element_mul (x y : Z) : center_element (x * y) = center_element x * center_element y.
Proof. apply val_inj; reflexivity. Qed.

Definition center_value (z : Z) : G := distinguished L (center_element z).

Lemma center_value_mul (x y : Z) : center_value (x * y) = center_value x * center_value y.
Proof.
change (distinguished L (center_element (x * y)) =
  linking_compose L (distinguished L (center_element x)) (distinguished L (center_element y))).
rewrite center_element_mul; exact: distinguished_mul.
Qed.

Definition center_embedding : {morphism [set: Z] >-> G}.
Proof.
apply: (Morphism (mfun := center_value)); move=> x y _ _; exact: center_value_mul.
Defined.

Lemma center_embedding_apply (z : Z) : center_embedding z = distinguished L (center_element z).
Proof. reflexivity. Qed.

Lemma center_embedding_injective : injective center_embedding.
Proof.
move=> x y he; apply val_inj.
have hc : center_element x = center_element y := @distinguished_injective S F L P _ _ he.
exact (congr1 (fun z : [subg (val P)] => val z) hc).
Qed.

Lemma center_embedding_injm : 'injm center_embedding.
Proof. apply/injmP=> x y _ _; exact: center_embedding_injective. Qed.

Lemma center_projection_one (z : Z) : pr (center_embedding z) = 1.
Proof.
apply (proj2 (@projection_eq_one_iff S F L P (center_embedding z))).
exact: projection_central_distinguished.
Qed.

Theorem projection_eq_one_center (a : G) :
    pr a = 1 <-> exists z : Z, center_embedding z = a.
Proof.
split.
- move=> /(proj1 (@projection_eq_one_iff S F L P a)) ha.
  have hp : linking_projection L (linking_identity L P) = linking_projection L a.
    by rewrite projection_identity ha.
  have [z [hz _]] := proj1 (@central_fiber S F L P P (linking_identity L P) a) hp.
  exists z; change (linking_compose L (center_embedding z) (linking_identity L P) = a) in hz.
  by rewrite linking_id_right in hz.
- move=> [z <-]; exact: center_projection_one.
Qed.

Theorem projection_kernel : 'ker pr = center_embedding @* [set: Z].
Proof.
apply/setP=> a; apply/idP/idP.
- move/(kerP pr (in_setT a))=> ha.
  have [z hz] := proj1 (projection_eq_one_center a) ha.
  apply/morphimP; exists z; [by rewrite inE | by rewrite inE | exact: esym hz].
- move/morphimP=> [z _ _ ->]; apply/(kerP pr (in_setT _)); exact: center_projection_one.
Qed.

Lemma projection_kernel_card : #|'ker pr| = #|'Z(val P)|.
Proof.
rewrite projection_kernel (card_injm center_embedding_injm (subxx [set: Z])) cardsT card_sub.
reflexivity.
Qed.

Theorem automorphism_order : #|G| = (#|'Z(val P)| * #|AF|)%N.
Proof.
have him : [set: H] \subset pr @* [set: G] by rewrite projection_image.
have hc := card_morphpre him.
rewrite morphpreT projection_kernel_card !cardsT card_sub in hc.
exact hc.
Qed.

Theorem projection_preimage_card (K : {group H}) :
    #|pr @*^-1 K| = (#|'Z(val P)| * #|K|)%N.
Proof.
rewrite card_morphpre ?projection_kernel_card // projection_image; exact: subsetT.
Qed.
End Kernel.
End DPLinkingAutomorphismKernel.

Check DPLinkingAutomorphismKernel.projection_kernel.
Check DPLinkingAutomorphismKernel.automorphism_order.
Check DPLinkingAutomorphismKernel.projection_preimage_card.
Print Assumptions DPLinkingAutomorphismKernel.projection_kernel.
Print Assumptions DPLinkingAutomorphismKernel.automorphism_order.
Print Assumptions DPLinkingAutomorphismKernel.projection_preimage_card.
