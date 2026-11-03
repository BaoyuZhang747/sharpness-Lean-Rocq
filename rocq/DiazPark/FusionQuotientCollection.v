From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import Category CategoryIsomorphism CategoryReindex
  FusionMaps FusionSystems FusionOrbit FusionSaturation FusionQuotientMaps
  FusionQuotientConstruction FusionQuotientNormalization FusionQuotientCentric
  FusionQuotientOrbitMaps FusionQuotientOrbitIso.
Import DPFusion DPFusionQuotientConstruction DPFusionQuotientNormalization
  DPFusionOrbit DPFusionQuotientOrbitMaps DPFusionQuotientOrbitIso.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientCollection.
Section Collection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.

(** The actual collection of ambient subgroups, without a chosen lift or
    representative as part of the object. *)
Definition collection (P : {group S}) : bool :=
  (Z \subset P) && DPFusionSystem.centric (system cZ) (P / Z)%G.
Definition collection_object := {P : {group S} | collection P}.

Lemma collection_contains (P : collection_object) : Z \subset val P.
Proof. exact: (andP (valP P)).1. Qed.

Definition quotient_object (P : collection_object) : centric_object (system cZ) :=
  Sub (val P / Z)%G (andP (valP P)).2.

Lemma preimage_collection (P : centric_object (system cZ)) : collection (preimage (val P)).
Proof.
rewrite /collection kernel_sub_preimage /= preimage_quotient.
exact: valP.
Qed.

Definition preimage_object (P : centric_object (system cZ)) : collection_object :=
  Sub (preimage (val P)) (preimage_collection P).

Lemma quotient_preimage_cancel : cancel preimage_object quotient_object.
Proof. move=> P; apply: val_inj; exact: preimage_quotient. Qed.

Lemma preimage_quotient_cancel : cancel quotient_object preimage_object.
Proof.
move=> P; apply: val_inj.
change (preimage (val P / Z)%G = val P).
exact (@preimage_of_quotient S F Z cZ (val P) (collection_contains P)).
Qed.

Theorem collection_centric (P : {group S}) : collection P -> DPFusionSystem.centric F P.
Proof.
move=> /andP[sZP hP].
have h := @DPFusionQuotientCentric.centric_preimage S F Z cZ (P / Z)%G hP.
by rewrite (preimage_of_quotient cZ sZP) in h.
Qed.

(** Literal full subcategory of the original orbit category. *)
Definition collection_category : category :=
  reindexed_category (orbit_category F) (fun P : collection_object => val P).

Variable p : nat.
Hypothesis pZ : p.-group Z.
Hypothesis sat : DPFusionSaturation.saturated F p.

Definition collection_to_preimage_isomorphism :
    category_isomorphism collection_category (preimage_category cZ).
Proof.
  refine (category_iso_trans
    (@reindex_equal_isomorphism (orbit_category F) collection_object
      (fun P => val P) (fun P => preimage (val (quotient_object P)))
      (fun P => esym (preimage_of_quotient cZ (collection_contains P)))) _).
  refine (category_iso_trans
    (category_iso_symm (@reindex_flat_isomorphism (orbit_category F)
      (centric_object (system cZ)) collection_object
      (fun P => preimage (val P)) quotient_object)) _).
  exact (@reindex_category_isomorphism (preimage_category cZ) collection_object
    quotient_object preimage_object quotient_preimage_cancel preimage_quotient_cancel).
Defined.

Definition collection_category_isomorphism :
    category_isomorphism collection_category (centric_orbit_category (system cZ)) :=
  category_iso_trans collection_to_preimage_isomorphism
    (quotient_category_isomorphism cZ pZ sat).

Definition collection_quotient_functor :=
  category_iso_forward collection_category_isomorphism.

Theorem collection_quotient_object (P : collection_object) :
  val (fobj collection_quotient_functor P) = (val P / Z)%G.
Proof. reflexivity. Qed.

Theorem collection_quotient_map (P Q : collection_object)
    (f : orbit_hom F (val P) (val Q)) :
  fmap collection_quotient_functor f = orbit_map cZ
    (@hom_transport (orbit_category F) (val P) (val Q)
      (preimage (val P / Z)%G) (preimage (val Q / Z)%G)
      (esym (preimage_of_quotient cZ (collection_contains P)))
      (esym (preimage_of_quotient cZ (collection_contains Q))) f).
Proof. reflexivity. Qed.

End Collection.
End DPFusionQuotientCollection.

Print Assumptions DPFusionQuotientCollection.collection_category_isomorphism.
Print Assumptions DPFusionQuotientCollection.collection_centric.
