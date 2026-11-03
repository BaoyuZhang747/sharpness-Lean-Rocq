(** The literal ambient-centric normalizer collection is isomorphic to the
    nested full subcategory used by the existing derived restriction theorem. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryIsomorphism
  CategoryIsomorphismAdjunction CategoryReindex CategoryAdjunction CategoryNaturalIso
  CategoryModules CategoryDerivedLimits CategoryDerivedAdjunction CategoryAtomicDeletionCore
  CategoryAtomicDeletionTheorem HomologicalModuleIso BarHigherLimitVanishing
  FusionMaps FusionSystems FusionOrbit FusionSaturation FusionRadical
  FusionCollectionAcyclicity FusionCollectionDegreewise.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects NormalizerChainNormalizer
  ChainNormalizerFusionModel ChainNormalizerFusionOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPLinkingChains DPNormalizerChain DPChainNormalizerFusionModel
  DPChainNormalizerFusionOrbit DiazParkHomologicalModuleIso DiazParkBarHigherLimitVanishing.
Local Open Scope group_scope.

Module DPChainNormalizerFusionCollectionAdapter.
Section Adapter.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Local Notation N := [the finGroupType of [subg (normalizer c)]%type].
Local Notation H := (local_system L c).
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.
Local Notation X := (collection_category L c).
Local Notation C := (fun P : {group N} => is_true (@ambient_centric S F c P)).
Local Notation Y := (DPFusionCollectionAcyclicity.collection_orbit_category H C).

Definition to_prop_object (P : X) : Y :=
  exist _ (@collection_local_object S F L c p sat P) (valP P).

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
  change (@hom_transport
    (reindexed_category (orbit_category H) (fun P : X => val P))
    _ _ _ _ (literal_roundtrip P) (literal_roundtrip Q) f = f).
  rewrite reindexed_hom_transport.
  cbn [fmap functor_comp functor_id to_prop to_literal to_prop_object to_literal_object].
  exact: (@hom_transport_loop (orbit_category H) (val P) (val Q)).
- apply: (@functor_ext_pointwise Y Y (functor_comp to_literal to_prop)
    (functor_id Y) prop_roundtrip).
  move=> P Q f.
  change (@hom_transport
    (reindexed_category (orbit_category H) (fun P : Y => val (proj1_sig P)))
    _ _ _ _ (prop_roundtrip P) (prop_roundtrip Q) f = f).
  rewrite reindexed_hom_transport.
  exact: (@hom_transport_loop (orbit_category H)
    (val (proj1_sig P)) (val (proj1_sig Q))).
Defined.

Lemma collection_inclusion_commutes :
  functor_comp to_prop (@full_inclusion (centric_orbit_category H)
    (@DPFusionCollectionAcyclicity.centric_collection N H C)) =
  @collection_local_functor S F L c p sat.
Proof. reflexivity. Qed.

Variable R : pzRingType.
Definition literal_restriction (D : module_codiagram R (centric_orbit_category H)) :
    module_codiagram R X :=
  functor_comp (functor_op (@collection_local_functor S F L c p sat)) D.

Definition restriction_adapter_iso (D : module_codiagram R (centric_orbit_category H)) n :
  @isomorphism (module_category R)
    (derived_limit R (fobj (DPFusionCollectionAcyclicity.collection_restriction H C R) D) n)
    (derived_limit R (literal_restriction D) n).
Proof.
exact (nat_iso_component
  (derived_left_adjoint_nat_iso R
    (adjunction_op (category_iso_adjunction (category_iso_symm collection_category_iso))) n)
  (fobj (DPFusionCollectionAcyclicity.collection_restriction H C R) D)).
Defined.

Lemma restriction_adapter_naturality
    (D E : module_codiagram R (centric_orbit_category H)) (u : nat_trans D E) n
    (q : derived_limit R
      (fobj (DPFusionCollectionAcyclicity.collection_restriction H C R) D) n) :
  module_hom_fun (derived_limit_map R
    (nat_whisker_left (functor_op (@collection_local_functor S F L c p sat)) u) n)
    (module_hom_fun (iso_hom (restriction_adapter_iso D n)) q) =
  module_hom_fun (iso_hom (restriction_adapter_iso E n))
    (module_hom_fun (derived_limit_map R
      (fmap (DPFusionCollectionAcyclicity.collection_restriction H C R) u) n) q).
Proof.
pose e := derived_left_adjoint_nat_iso R
  (adjunction_op (category_iso_adjunction (category_iso_symm collection_category_iso))) n.
have hn := naturality (iso_hom e)
  (fmap (DPFusionCollectionAcyclicity.collection_restriction H C R) u).
exact: esym (congr1 (fun k => module_hom_fun k q) hn).
Qed.

(** Explicit intermediate: the final application must supply the proved
    local saturation and centric-radical containment for the actual chain. *)
Hypothesis pN : p.-group [set: N].
Hypothesis satH : DPFusionSaturation.saturated H p.
Hypothesis contains_radical : forall P, DPFusionSystem.centric H P ->
  DPFusionRadical.radical H p P -> C P.

Definition collection_derived_iso (D : module_codiagram R (centric_orbit_category H)) n :
  @isomorphism (module_category R) (derived_limit R D n)
    (derived_limit R (literal_restriction D) n) :=
  module_iso_comp
    (@DPFusionCollectionDegreewise.collection_derived_iso N H p pN satH C
      (@ambient_centric_conjugate S F L c p sat)
      (@ambient_centric_overgroup S F c) contains_radical R D n)
    (restriction_adapter_iso D n).

End Adapter.
End DPChainNormalizerFusionCollectionAdapter.
