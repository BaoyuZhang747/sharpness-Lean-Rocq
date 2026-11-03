(** Actual image factorization in the pointed normalized-subgroup category. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient pgroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionOrbitRanks
  FusionConjugacy FusionSaturation.
From DiazParkV16b Require Import NormalizerPointedSubgroupExtensions NormalizerPointedSubgroups
  NormalizerPointedSubgroupImages NormalizerPointedSubgroupImageInverse
  NormalizerPointedSubgroupImageIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionOrbit DPNormalizerSubgroupExtensions DPNormalizerPointedSubgroups
  DPNormalizerSubgroupImages DPNormalizerSubgroupImageInverse.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPNormalizerPointedSubgroupImageFactorization.
Section Factorization.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : centric_object F.
Local Notation C := (pointed_category P).
Local Notation OC := (centric_orbit_category F).

Lemma acting_card (A : C) : #|val (acting A)| = #|val P|.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- exact: DPFusionRanks.orbit_rank_le (iso_inv (point A)).
- exact: DPFusionRanks.orbit_rank_le (iso_hom (point A)).
Qed.

Lemma raw_onto (A B : C) (g : DPFusionSystem.arrow F (val (acting A)) (val (acting B))) :
  image (val g) = val (acting B).
Proof. apply DPFusionRanks.raw_equal_rank_image; by rewrite !acting_card. Qed.

Record extension_data (A B : C) := {
  data_raw : DPFusionSystem.arrow F (val (acting A)) (val (acting B));
  data_point : @Category.compose OC P (acting A) (acting B) (iso_hom (point A))
    (orbit_class data_raw) = iso_hom (point B);
  data_extension : extension F (subgroup A) (subgroup B) (val data_raw)
}.

Lemma extension_data_exists (A B : C) (h : hom C A B) : exists d : extension_data A B, True.
Proof.
change (related A B) in h; case: h=> g [hg [a]].
exists (@Build_extension_data A B g hg a); exact I.
Qed.

Definition chosen_data (A B : C) (h : hom C A B) : extension_data A B :=
  proj1_sig (cid (extension_data_exists h)).

Definition arrow_image (A B : C) (h : hom C A B) : {group S} :=
  subgroup_image (data_extension (chosen_data h)).

Lemma arrow_image_sub (A B : C) (h : hom C A B) : arrow_image h \subset subgroup B.
Proof. exact: subgroup_image_sub. Qed.

Definition image_object (A B : C) (h : hom C A B) : C :=
  @Build_object S F P (acting B) (point B) (arrow_image h)
    (subgroup_image_centric (data_extension (chosen_data h)) (subgroup_centric A))
    (subgroup_image_normalized (data_extension (chosen_data h)) (normalizes A)
      (raw_onto (data_raw (chosen_data h)))).

Definition to_image (A B : C) (h : hom C A B) : hom C A (image_object h).
Proof.
change (related A (image_object h)).
exists (data_raw (chosen_data h)); split; first exact (data_point (chosen_data h)).
constructor; exact (image_extension (data_extension (chosen_data h))).
Defined.

Definition from_image (A B : C) (h : hom C A B) : hom C (image_object h) A.
Proof.
change (related (image_object h) A).
pose d := chosen_data h.
pose invf : DPFusionSystem.arrow F (val (acting B)) (val (acting A)) :=
  Sub (DPFusionConjugacy.onto_inverse (raw_onto (data_raw d)))
    (DPFusionConjugacy.onto_inverse_allowed (raw_onto (data_raw d)) (valP (data_raw d))).
exists invf; split.
- change (@Category.compose OC P (acting B) (acting A) (iso_hom (point B))
    (orbit_class invf) = iso_hom (point A)).
  rewrite -(data_point d) Category.compose_assoc.
  have hi := iso_hom_inv (DPFusionRanks.raw_onto_iso (raw_onto (data_raw d))).
  change (orbit_compose (orbit_class (data_raw d)) (orbit_class invf) =
    orbit_identity F (val (acting A))) in hi.
  change (@Category.compose OC P (acting A) (acting A) (iso_hom (point A))
    (orbit_compose (orbit_class (data_raw d)) (orbit_class invf)) = iso_hom (point A)).
  by rewrite hi compose_id_right.
- constructor; exact (inverse_extension (data_extension d) (raw_onto (data_raw d))).
Defined.

Definition image_iso (A B : C) (h : hom C A B) : @isomorphism C A (image_object h).
Proof.
refine (@Build_isomorphism C A (image_object h) (to_image h) (from_image h) _ _);
  apply hom_unique.
Defined.

Definition image_inclusion (A B : C) (h : hom C A B) : hom C (image_object h) B.
Proof.
change (related (image_object h) B).
exists (DPFusionSystem.arrow_identity F (val (acting B))); split; first exact (compose_id_right _).
constructor.
pose V := (val (acting B) <*> arrow_image h)%G.
refine (@Build_extension S F (arrow_image h) (subgroup B)
  (val (acting B)) (val (acting B)) (identity (val (acting B))) V
  (joing_subl _ _) (joing_subr _ _) (inclusion (subsetT V))
  (DPFusionSystem.inclusion_allowed F _) _ _).
- move=> x hx; by rewrite inclusion_in ?(subsetP (joing_subl _ _) _ hx) // identity_in.
- move=> x hx; rewrite inclusion_in ?(subsetP (joing_subr _ _) _ hx) //.
  exact: subsetP (arrow_image_sub h) _ hx.
Defined.

Lemma image_factorization (A B : C) (h : hom C A B) :
  Category.compose (iso_hom (image_iso h)) (image_inclusion h) = h.
Proof. exact: hom_unique. Qed.

Lemma extension_card_le (A B : C) (h : hom C A B) : #|subgroup A| <= #|subgroup B|.
Proof.
rewrite -(subgroup_image_card (data_extension (chosen_data h))).
exact: subset_leq_card (arrow_image_sub h).
Qed.

Lemma arrow_image_eq_target (A B : C) (h : hom C A B) (k : hom C B A) :
  arrow_image h = subgroup B.
Proof.
apply val_inj; apply/eqP; rewrite eqEcard arrow_image_sub.
rewrite /arrow_image subgroup_image_card; exact: extension_card_le k.
Qed.
End Factorization.
End DPNormalizerPointedSubgroupImageFactorization.
