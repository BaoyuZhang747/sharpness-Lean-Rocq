(** Finite actual automorphism groups.  A linking endomorphism has an
    inverse because right composition is injective on its finite Hom set. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup center boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem
  LinkingSystemFinite LinkingSystemCancellation LinkingSystemFactorization LinkingSystemRestrictions.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingFinite DPLinkingCancellation.
Local Open Scope group_scope.

Module DPLinkingAutomorphisms.

Lemma categorical_isomorphism_ext (C : category) (x y : C)
    (e e' : @isomorphism C x y) : iso_hom e = iso_hom e' -> e = e'.
Proof.
case: e => f g fg gf; case: e' => f' g' fg' gf' /= he; subst f'.
have hg : g = g'.
  rewrite -(compose_id_right g) -fg' -compose_assoc gf compose_id_left; reflexivity.
subst g'; f_equal; apply Prop_irrelevance.
Qed.

Section Automorphisms.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable P : DPFusionOrbit.centric_object F.
Local Notation E := (hom_finType L P P).

Definition endomorphism_mul (f g : E) : E := linking_compose L f g.
Definition endomorphism_one : E := linking_identity L P.
Definition endomorphism_inverse (f : E) : E :=
  @invF E (fun g : E => linking_compose L g f)
    (@compose_right_injective S F L P P P f) endomorphism_one.

Lemma endomorphism_mul_assoc : associative endomorphism_mul.
Proof. move=> f g h; symmetry; exact: linking_assoc. Qed.

Lemma endomorphism_one_left : left_id endomorphism_one endomorphism_mul.
Proof. exact: linking_id_left. Qed.

Lemma endomorphism_inverse_left : left_inverse endomorphism_one endomorphism_inverse endomorphism_mul.
Proof.
move=> f; exact (@f_invF E (fun g : E => linking_compose L g f)
  (@compose_right_injective S F L P P P f) endomorphism_one).
Qed.

Definition automorphism_group : finGroupType :=
  HB.pack E (Finite_isGroup.Build E endomorphism_mul_assoc
    endomorphism_one_left endomorphism_inverse_left).

Lemma automorphism_group_carrier : (automorphism_group : Type) = linking_hom L P P.
Proof. reflexivity. Qed.

Lemma automorphism_mul (f g : automorphism_group) : f * g = linking_compose L f g.
Proof. reflexivity. Qed.

Lemma automorphism_one : (1 : automorphism_group) = linking_identity L P.
Proof. reflexivity. Qed.

Definition automorphism_isomorphism (f : automorphism_group) :
    @isomorphism (linking_category L) P P.
Proof.
refine (@Build_isomorphism (linking_category L) P P f f^-1 _ _).
- change (f * f^-1 = (1 : automorphism_group)); exact: mulgV.
- change (f^-1 * f = (1 : automorphism_group)); exact: mulVg.
Defined.

Definition isomorphism_automorphism (e : @isomorphism (linking_category L) P P) :
    automorphism_group := iso_hom e.

Lemma automorphism_isomorphismK : cancel automorphism_isomorphism isomorphism_automorphism.
Proof. by []. Qed.

Lemma isomorphism_automorphismK : cancel isomorphism_automorphism automorphism_isomorphism.
Proof. move=> e; apply categorical_isomorphism_ext; reflexivity. Qed.

(** The finite type here is literally the original categorical isomorphism
    record, not merely a set with its expected cardinality. *)
Definition categorical_automorphism_finType : finType := can_type isomorphism_automorphismK.

Definition distinguished_map (x : [subg (val P)]) : automorphism_group := distinguished L x.

Lemma distinguished_map_morphic : morphic [set: [subg (val P)]] distinguished_map.
Proof. apply/morphicP => x y _ _; exact: distinguished_mul. Qed.

Definition distinguished_morphism : {morphism [set: [subg (val P)]] >-> automorphism_group} :=
  [morphism of morphm distinguished_map_morphic].

Lemma distinguished_morphism_injective : injective distinguished_morphism.
Proof. exact: distinguished_injective. Qed.
End Automorphisms.
End DPLinkingAutomorphisms.

Check DPLinkingAutomorphisms.automorphism_group.
Check DPLinkingAutomorphisms.categorical_automorphism_finType.
Check DPLinkingAutomorphisms.distinguished_morphism.
Print Assumptions DPLinkingAutomorphisms.automorphism_group.
Print Assumptions DPLinkingAutomorphisms.isomorphism_automorphismK.
Print Assumptions DPLinkingAutomorphisms.distinguished_morphism_injective.
