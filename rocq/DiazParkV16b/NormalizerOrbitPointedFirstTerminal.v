(** The isomorphism-pointed first-entry comma has an actual singleton terminal object. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryComma CategoryLimits FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices NormalizerChainExtensions
  NormalizerOrbitPairCategory NormalizerOrbitCommaImageObjects NormalizerOrbitPointedFirst
  NormalizerPointedSubgroups NormalizerPointedSubgroupExtensions NormalizerPointedSubgroupImages
  NormalizerPointedSubgroupImageFactorization NormalizerOrbitPointedFirstComma.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPLinkingChains DPNormalizerOrbitPointedFirstComma.
Local Open Scope group_scope.

Module DPNormalizerOrbitPointedFirstTerminal.
Section Terminal.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : DPFusionOrbit.centric_object F.
Local Notation CP := (DPNormalizerOrbitCommaImage.pointed_category P).
Local Notation SP := (DPNormalizerPointedSubgroups.pointed_category P).
Local Notation PC := (DPNormalizerOrbitPair.pair_category F).
Local Notation OC := (DPFusionOrbit.centric_orbit_category F).
Local Notation E := (DPNormalizerOrbitPointedFirst.first_functor P).
Variable B : SP.
Variable Y : first_points B.
Let X := point_chain Y.
Let A := DPNormalizerOrbitCommaImage.pointed_pair X.
Let c := DPNormalizerOrbitPair.chain_of A.
Let k := iso_inv (point_iso Y).
Let d := DPNormalizerPointedSubgroupImageFactorization.chosen_data k.

Definition singleton_selector : DPNormalizerChainIndices.selector c
  (singleton (singleton_centric B)).
Proof.
apply: (Sub [ffun _ => ord0]); apply/DPNormalizerChainIndices.increasingP=> i j.
by rewrite (ord1 i) (ord1 j) ltnn.
Defined.

Definition terminal_extension : DPNormalizerChainExtensions.extension c
  (singleton (singleton_centric B)) (val (DPNormalizerPointedSubgroupImageFactorization.data_raw d)).
Proof.
pose a := DPNormalizerPointedSubgroupImageFactorization.data_extension d.
refine (@DPNormalizerChainExtensions.Build_extension S F c (singleton (singleton_centric B))
  _ _ _ singleton_selector (DPNormalizerSubgroupExtensions.carrier a)
  (DPNormalizerSubgroupExtensions.acting_sub a) _
  (DPNormalizerSubgroupExtensions.extension_map a)
  (DPNormalizerSubgroupExtensions.extension_allowed a)
  (DPNormalizerSubgroupExtensions.on_acting a) _).
- rewrite /singleton_selector /DPNormalizerChainIndices.index /= ffunE.
  exact (DPNormalizerSubgroupExtensions.subgroup_sub a).
- move=> i; rewrite /singleton_selector /DPNormalizerChainIndices.index /= ffunE
    /subgroup singleton_entry.
  exact (congr1 (fun H : {group S} => (H : {set S}))
    (DPNormalizerPointedSubgroupImageFactorization.arrow_image_eq_target k (iso_hom (point_iso Y)))).
Defined.

Definition terminal_pair_map : hom PC A (singleton_pair B) :=
  @DPNormalizerOrbitPair.hom_of_extension S F A (singleton_pair B)
    (DPNormalizerPointedSubgroupImageFactorization.data_raw d) terminal_extension.

Definition terminal_chain_map : hom CP X (singleton_point B).
Proof.
refine (@Build_costructured_hom (opposite PC) (opposite OC)
  (functor_op (DPNormalizerOrbitPair.forget F)) P
  (DPNormalizerOrbitCommaImage.pointed_under (singleton_point B))
  (DPNormalizerOrbitCommaImage.pointed_under X) terminal_pair_map _).
exact (DPNormalizerPointedSubgroupImageFactorization.data_point d).
Defined.

Definition terminal_map : hom (first_points B) Y (terminal_point B).
Proof.
refine (@Build_costructured_hom (opposite CP) (opposite SP) (functor_op E) B
  (point_under (terminal_point B)) (point_under Y) terminal_chain_map _).
exact (@DPNormalizerPointedSubgroups.hom_unique S F P B (fobj E (singleton_point B)) _ _).
Defined.
End Terminal.

Definition first_points_terminal (S : finGroupType) (F : DPFusionSystem.system S)
    (P : DPFusionOrbit.centric_object F)
    (B : DPNormalizerPointedSubgroups.pointed_category P) :
    CategoryLimits.terminal_object (first_points B).
Proof.
refine (@Build_terminal_object (first_points B) (terminal_point B) (@terminal_map S F P B) _).
intros; apply first_under_hom_unique.
Defined.
End DPNormalizerOrbitPointedFirstTerminal.
