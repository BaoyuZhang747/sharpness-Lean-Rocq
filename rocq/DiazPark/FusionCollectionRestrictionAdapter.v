(** Literal ambient-subgroup collections and the nested Prop full subcategory
    used by finite atomic deletion are genuinely isomorphic categories. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryIsomorphism
  CategoryIsomorphismAdjunction CategoryReindex CategoryAdjunction CategoryNaturalIso
  CategoryModules CategoryDerivedLimits CategoryDerivedAdjunction
  CategoryAtomicDeletionCore CategoryAtomicDeletionTheorem
  BarHigherLimitVanishing FusionMaps FusionSystems FusionOrbit FusionSaturation
  FusionQuotientMaps FusionQuotientConstruction FusionQuotientCollection
  FusionQuotientCollectionClosure FusionQuotientRadical
  FusionCollectionAcyclicity FusionCollectionAcyclicityUnconditional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPFusionQuotientCollection DiazParkBarHigherLimitVanishing.
Local Open Scope group_scope.

Module DPFusionCollectionAdapter.
Section Adapter.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Local Notation X := (collection_category cZ).
Local Notation H := (fun P : {group S} => is_true (collection cZ P)).
Local Notation Y := (DPFusionCollectionAcyclicity.collection_orbit_category F H).

Definition to_prop_object (P : X) : Y :=
  exist _ (Sub (val P) (@collection_centric S F Z cZ (val P) (valP P))) (valP P).
Definition to_literal_object (P : Y) : X :=
  Sub (val (proj1_sig P)) (proj2_sig P).

Definition to_prop : functor X Y.
Proof.
refine (@Build_functor X Y to_prop_object (fun P Q f => f) _ _); reflexivity.
Defined.
Definition to_literal : functor Y X.
Proof.
refine (@Build_functor Y X to_literal_object (fun P Q f => f) _ _); reflexivity.
Defined.

Lemma literal_roundtrip P : to_literal_object (to_prop_object P) = P.
Proof. apply val_inj; reflexivity. Qed.
Lemma prop_roundtrip P : to_prop_object (to_literal_object P) = P.
Proof.
apply eq_sig_hprop.
- intros; apply Prop_irrelevance.
- apply val_inj; reflexivity.
Qed.

Definition collection_category_iso : category_isomorphism X Y.
Proof.
refine (@Build_category_isomorphism X Y to_prop to_literal _ _).
- apply: (@functor_ext_pointwise X X (functor_comp to_prop to_literal)
    (functor_id X) literal_roundtrip).
  move=> P Q f.
  rewrite reindexed_hom_transport.
  cbn [fmap functor_comp functor_id to_prop to_literal to_prop_object to_literal_object].
  exact: (@hom_transport_loop (orbit_category F) (val P) (val Q)).
- apply: (@functor_ext_pointwise Y Y (functor_comp to_literal to_prop)
    (functor_id Y) prop_roundtrip).
  move=> P Q f.
  change (@hom_transport
    (reindexed_category (orbit_category F) (fun P : Y => val (proj1_sig P)))
    _ _ _ _ (prop_roundtrip P) (prop_roundtrip Q) f = f).
  rewrite reindexed_hom_transport.
  exact: (@hom_transport_loop (orbit_category F)
    (val (proj1_sig P)) (val (proj1_sig Q))).
Defined.

Definition collection_centric_inclusion : functor X (centric_orbit_category F) :=
  functor_comp to_prop (@full_inclusion (centric_orbit_category F)
    (@DPFusionCollectionAcyclicity.centric_collection S F H)).

Lemma collection_inclusion_commutes :
  functor_comp collection_centric_inclusion (centric_inclusion F) =
    reindex_inclusion (orbit_category F) (fun P : collection_object cZ => val P).
Proof.
apply: (@functor_extensionality X (orbit_category F)
  (functor_comp collection_centric_inclusion (centric_inclusion F))
  (reindex_inclusion (orbit_category F) (fun P : collection_object cZ => val P))
  (Logic.eq_refl _)); reflexivity.
Qed.

Variable R : pzRingType.
Definition literal_restriction (D : module_codiagram R (centric_orbit_category F)) :
    module_codiagram R X := functor_comp (functor_op collection_centric_inclusion) D.

Definition restriction_adapter_iso (D : module_codiagram R (centric_orbit_category F)) n :
  @isomorphism (module_category R)
    (derived_limit R
      (fobj (DPFusionCollectionAcyclicity.collection_restriction F H R) D) n)
    (derived_limit R (literal_restriction D) n).
Proof.
exact (nat_iso_component
  (derived_left_adjoint_nat_iso R
    (adjunction_op (category_iso_adjunction (category_iso_symm collection_category_iso))) n)
  (fobj (DPFusionCollectionAcyclicity.collection_restriction F H R) D)).
Defined.

Lemma restriction_adapter_naturality
    (D E : module_codiagram R (centric_orbit_category F)) (u : nat_trans D E) n
    (q : derived_limit R
      (fobj (DPFusionCollectionAcyclicity.collection_restriction F H R) D) n) :
  module_hom_fun (derived_limit_map R
    (nat_whisker_left (functor_op collection_centric_inclusion) u) n)
    (module_hom_fun (iso_hom (restriction_adapter_iso D n)) q) =
  module_hom_fun (iso_hom (restriction_adapter_iso E n))
    (module_hom_fun (derived_limit_map R
      (fmap (DPFusionCollectionAcyclicity.collection_restriction F H R) u) n) q).
Proof.
pose e := derived_left_adjoint_nat_iso R
  (adjunction_op (category_iso_adjunction (category_iso_symm collection_category_iso))) n.
have hn := naturality (iso_hom e)
  (fmap (DPFusionCollectionAcyclicity.collection_restriction F H R) u).
exact: esym (congr1 (fun k => module_hom_fun k q) hn).
Qed.

Lemma restriction_adapter_positive (D : module_codiagram R (centric_orbit_category F)) :
  derived_positive_zero
    (fobj (DPFusionCollectionAcyclicity.collection_restriction F H R) D) <->
  derived_positive_zero (literal_restriction D).
Proof.
split=> h n; [apply/(module_iso_zero_iff (restriction_adapter_iso D n.+1)) |
  apply/(module_iso_zero_iff (restriction_adapter_iso D n.+1))]; exact: h.
Qed.

Lemma restriction_adapter_all (D : module_codiagram R (centric_orbit_category F)) :
  derived_all_zero
    (fobj (DPFusionCollectionAcyclicity.collection_restriction F H R) D) <->
  derived_all_zero (literal_restriction D).
Proof.
split=> h n; [apply/(module_iso_zero_iff (restriction_adapter_iso D n)) |
  apply/(module_iso_zero_iff (restriction_adapter_iso D n))]; exact: h.
Qed.

Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis pZ : p.-group Z.
Hypothesis sat : DPFusionSaturation.saturated F p.

Theorem literal_collection_acyclic_iff
    (D : module_codiagram R (centric_orbit_category F)) :
  derived_positive_zero D <-> derived_positive_zero (literal_restriction D).
Proof.
transitivity (derived_positive_zero
  (fobj (DPFusionCollectionAcyclicity.collection_restriction F H R) D)).
- exact (@DPFusionCollection.collection_acyclic_iff S F p pS sat H
    (@DPFusionQuotientCollectionClosure.collection_conjugate S F Z cZ)
    (@DPFusionQuotientCollectionClosure.collection_overgroup S F Z cZ)
    (@DPFusionQuotientRadical.centric_radical_collection S F Z cZ p pZ) R D).
- exact: restriction_adapter_positive.
Qed.

Theorem literal_collection_all_zero_iff
    (D : module_codiagram R (centric_orbit_category F)) :
  derived_all_zero D <-> derived_all_zero (literal_restriction D).
Proof.
transitivity (derived_all_zero
  (fobj (DPFusionCollectionAcyclicity.collection_restriction F H R) D)).
- exact (@DPFusionCollection.collection_all_zero_iff S F p pS sat H
    (@DPFusionQuotientCollectionClosure.collection_conjugate S F Z cZ)
    (@DPFusionQuotientCollectionClosure.collection_overgroup S F Z cZ)
    (@DPFusionQuotientRadical.centric_radical_collection S F Z cZ p pZ) R D).
- exact: restriction_adapter_all.
Qed.

End Adapter.
End DPFusionCollectionAdapter.
