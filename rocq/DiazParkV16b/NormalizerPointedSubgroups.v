(** The actual pointed normalized-subgroup enlargement category.  Arrows
    retain existence of simultaneous fusion extensions. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import NormalizerPointedSubgroupExtensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPNormalizerSubgroupExtensions.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPNormalizerPointedSubgroups.
Section Category.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : centric_object F.
Local Notation C := (centric_orbit_category F).

Record object := {
  acting : centric_object F;
  point : @isomorphism C P acting;
  subgroup : {group S};
  subgroup_centric : DPFusionSystem.centric F subgroup;
  normalizes : val acting \subset 'N(subgroup)
}.

Definition related (A B : object) : Prop :=
  exists f : DPFusionSystem.arrow F (val (acting A)) (val (acting B)),
    @compose C P (acting A) (acting B) (iso_hom (point A)) (orbit_class f) = iso_hom (point B) /\
    inhabited (extension F (subgroup A) (subgroup B) (val f)).

Lemma related_reflexive A : related A A.
Proof.
exists (DPFusionSystem.arrow_identity F (val (acting A))); split.
- exact (compose_id_right (iso_hom (point A))).
- constructor; exact (identity_extension F (val (acting A)) (subgroup A)).
Qed.

Lemma related_transitive A B D : related A B -> related B D -> related A D.
Proof.
move=> [f [hf [a]]] [g [hg [b]]].
exists (DPFusionSystem.arrow_compose f g); split.
- rewrite -orbit_compose_class.
  change (@compose C P (acting A) (acting D) (iso_hom (point A))
    (@compose C (acting A) (acting B) (acting D) (orbit_class f) (orbit_class g)) = iso_hom (point D)).
  by rewrite -compose_assoc hf hg.
- constructor; exact (compose_extension a b).
Qed.

Definition pointed_category : category.
Proof.
refine (@Build_category object related related_reflexive
  (fun A B D f g => related_transitive f g) _ _ _); intros; apply Prop_irrelevance.
Defined.

Lemma hom_unique (A B : pointed_category) (f g : hom pointed_category A B) : f = g.
Proof. change (@eq (related A B) f g); apply Prop_irrelevance. Qed.
End Category.
End DPNormalizerPointedSubgroups.
