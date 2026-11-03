(** The actual image point has the comma-category universal property.
    Extension representatives are corrected by a target-inner conjugation. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient boolp.
From DiazPark Require Import Category CategoryComma FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import NormalizerOrbitPairCategory NormalizerChainExtensions
  NormalizerChainExtensionRepresentatives NormalizerOrbitCommaImageObjects.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPNormalizerOrbitPair DPNormalizerOrbitCommaImage.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPNormalizerOrbitCommaImageUniversal.
Section Universal.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : centric_object F.
Local Notation OC := (centric_orbit_category F).
Local Notation PC := (pair_category F).
Local Notation UC := (under_category P).
Variable Y : pointed_object P.
Variable X : UC.
Variable f : hom UC (pointed_under Y) X.

Definition lift_orbit : hom OC (acting (pointed_pair Y)) (acting (image_pair X)) :=
  Category.compose (iso_inv (pointed_iso Y)) (iso_hom (image_iso X)).

Lemma lift_orbit_factorization :
  @Category.compose OC (acting (pointed_pair Y)) (acting (image_pair X))
    (acting (costructured_source X)) lift_orbit (val (image_pair_inclusion X)) =
    val (costructured_map f).
Proof.
rewrite /lift_orbit compose_assoc image_factorization.
have hf := costructured_commutes f.
change (Category.compose (iso_hom (pointed_iso Y)) (val (costructured_map f)) =
  costructured_arrow X) in hf.
by rewrite -hf -compose_assoc iso_inv_hom compose_id_left.
Qed.

Definition lift_pair : hom PC (pointed_pair Y) (image_pair X).
Proof.
apply: (Sub lift_orbit); apply/asboolP.
pose g : DPFusionSystem.arrow F (val (acting (pointed_pair Y))) (val (image_object X)) :=
  repr lift_orbit.
have hg : orbit_class g = lift_orbit := reprK lift_orbit.
exists g; split=> //.
have [f0 [hf0 [a]]] := hom_compatible (costructured_map f).
pose inc : DPFusionSystem.arrow F (val (image_object X)) (val (acting (costructured_source X))) :=
  Sub (DPFusion.inclusion (DPFusion.image_sub (val (image_raw X))))
    (DPFusionSystem.inclusion_allowed F _).
have he : orbit_class f0 = orbit_class (DPFusionSystem.arrow_compose g inc).
  rewrite -orbit_compose_class hg hf0.
  exact: esym lift_orbit_factorization.
pose a' := DPNormalizerChainExtensionRepresentatives.of_orbit_eq
  (acting_normalizes (costructured_source X)) a he.
constructor.
apply: (DPNormalizerChainExtensionRepresentatives.change_codomain a').
move=> x hx; rewrite /DPFusionSystem.arrow_compose /= DPFusion.compose_in //.
by rewrite DPFusion.inclusion_in ?DPFusion.map_into.
Defined.

Definition image_lift : hom UC (pointed_under Y) (pointed_under (image_point X)).
Proof.
refine (@Build_costructured_hom (opposite PC) (opposite OC) (functor_op (forget F)) P
  (pointed_under (image_point X)) (pointed_under Y) lift_pair _).
change (Category.compose (iso_hom (pointed_iso Y)) lift_orbit = iso_hom (image_iso X)).
by rewrite /lift_orbit -compose_assoc iso_hom_inv compose_id_left.
Defined.

Lemma image_lift_deletion : Category.compose image_lift (image_deletion X) = f.
Proof. exact: pointed_source_hom_unique. Qed.

Theorem image_universal : exists! g : hom UC (pointed_under Y) (pointed_under (image_point X)),
  Category.compose g (image_deletion X) = f.
Proof.
exists image_lift; split; first exact image_lift_deletion.
move=> g _; exact: pointed_source_hom_unique.
Qed.
End Universal.
End DPNormalizerOrbitCommaImageUniversal.
