(** Actual image factorization in the structured comma of the pair forgetful
    functor.  A point carries an explicit isomorphism in the centric orbit category. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient boolp.
From DiazPark Require Import Category CategoryComma FusionMaps FusionSystems FusionOrbit
  FusionCentricBasics FusionCentricSpanNormalization FusionCentricRestriction.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainNormalizer
  NormalizerOrbitPairCategory NormalizerChainExtensionRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPNormalizerOrbitPair DPFusionCentricSpanNormalization.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPNormalizerOrbitCommaImage.
Section Image.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : centric_object F.
Local Notation OC := (centric_orbit_category F).
Local Notation PC := (pair_category F).
Definition under_category : category := structured_category (forget F) P.

Record pointed_object := {
  pointed_pair : PC;
  pointed_iso : @isomorphism OC P (acting pointed_pair)
}.

Definition pointed_under (Y : pointed_object) : under_category :=
  @Build_costructured_object (opposite PC) (opposite OC) (functor_op (forget F)) P
    (pointed_pair Y) (iso_hom (pointed_iso Y)).

Definition pointed_category : category.
Proof.
refine (@Build_category pointed_object
  (fun A B => hom under_category (pointed_under A) (pointed_under B))
  (fun A => Category.identity (pointed_under A))
  (fun A B C f g => Category.compose f g) _ _ _).
- intros; apply compose_id_left.
- intros; apply compose_id_right.
- intros; apply compose_assoc.
Defined.

Definition pointed_inclusion : functor pointed_category under_category.
Proof. refine (@Build_functor pointed_category under_category pointed_under (fun _ _ f => f) _ _); reflexivity. Defined.

Lemma pointed_source_hom_unique (Y : pointed_object) (X : under_category)
    (f g : hom under_category (pointed_under Y) X) : f = g.
Proof.
apply costructured_hom_ext; apply val_inj.
have hf := costructured_commutes f.
have hg := costructured_commutes g.
change (@Category.compose OC P (acting (pointed_pair Y)) (acting (costructured_source X))
  (iso_hom (pointed_iso Y)) (val (costructured_map f)) = costructured_arrow X) in hf.
change (@Category.compose OC P (acting (pointed_pair Y)) (acting (costructured_source X))
  (iso_hom (pointed_iso Y)) (val (costructured_map g)) = costructured_arrow X) in hg.
have he := congr1 (fun t => @Category.compose OC (acting (pointed_pair Y)) P
  (acting (costructured_source X)) (iso_inv (pointed_iso Y)) t) (eq_trans hf (esym hg)).
by rewrite -!compose_assoc iso_inv_hom !compose_id_left in he.
Qed.

Definition image_raw (X : under_category) :
  DPFusionSystem.arrow F (val P) (val (acting (costructured_source X))) :=
  repr (costructured_arrow X).

Definition image_object (X : under_category) : centric_object F :=
  Sub (DPFusion.image (val (image_raw X)))
    (DPFusionCentricBasics.centric_image (valP (image_raw X)) (valP P)).

Definition image_iso (X : under_category) : @isomorphism OC P (image_object X) :=
  @Build_isomorphism OC P (image_object X)
    (iso_hom (orbit_image_iso (image_raw X))) (iso_inv (orbit_image_iso (image_raw X)))
    (iso_hom_inv (orbit_image_iso (image_raw X))) (iso_inv_hom (orbit_image_iso (image_raw X))).

Definition image_pair (X : under_category) : PC :=
  Sub (image_object X, chain_of (costructured_source X))
    (subset_trans (DPFusion.image_sub (val (image_raw X)))
      (acting_normalizes (costructured_source X))).

Definition image_point (X : under_category) : pointed_object :=
  @Build_pointed_object (image_pair X) (image_iso X).

Definition image_pair_inclusion (X : under_category) : hom PC (image_pair X) (costructured_source X) :=
  @hom_of_extension S F (image_pair X) (costructured_source X)
    (Sub (DPFusion.inclusion (DPFusion.image_sub (val (image_raw X))))
      (DPFusionSystem.inclusion_allowed F _))
    (DPNormalizerChainExtensionRepresentatives.inclusion_extension
      (DPFusion.image_sub (val (image_raw X))) (chain_of (costructured_source X))).

Lemma image_factorization (X : under_category) :
  @Category.compose OC P (acting (image_pair X)) (acting (costructured_source X))
    (iso_hom (image_iso X)) (val (image_pair_inclusion X)) = costructured_arrow X.
Proof.
change (orbit_compose (iso_hom (orbit_image_iso (image_raw X)))
  (DPFusionCentricRestriction.orbit_inclusion F (DPFusion.image_sub (val (image_raw X)))) =
  costructured_arrow X).
rewrite orbit_image_factorization; exact: reprK.
Qed.

Definition image_deletion (X : under_category) :
  hom under_category (pointed_under (image_point X)) X.
Proof.
refine (@Build_costructured_hom (opposite PC) (opposite OC) (functor_op (forget F)) P
  X (pointed_under (image_point X)) (image_pair_inclusion X) _).
exact: image_factorization.
Defined.
End Image.
End DPNormalizerOrbitCommaImage.
