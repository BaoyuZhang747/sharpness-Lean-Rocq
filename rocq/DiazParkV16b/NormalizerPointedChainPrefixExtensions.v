(** Prefix extensions and literal deletion maps for strict normalizer chains. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryComma FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices NormalizerChainExtensions
  NormalizerChainNormalizer NormalizerOrbitPairCategory NormalizerOrbitCommaImageObjects
  NormalizerPointedChainPrefix.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPLinkingChains DPNormalizerChainIndices DPNormalizerChainExtensions
  DPNormalizerPointedChainPrefix.
Local Open Scope group_scope.

Module DPNormalizerPointedChainPrefixExtensions.
Section Extensions.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables c d : chain F.
Variables P Q : {group S}.
Variable f : DPFusion.map P Q.
Variable a : extension c d f.
Variable I : DPFusionOrbit.centric_object F.
Hypothesis hI : val I \proper val (bottom d).
Hypothesis hImage : map_morphism (extension_map a) @* val (bottom c) = val I.

Lemma prefix_index_positive : 0 < index (indices a) ord0.
Proof.
rewrite lt0n; apply/eqP=> he.
have ei : index (indices a) ord0 = ord0 by apply val_inj.
have hi := entry_images a ord0; rewrite ei in hi.
have hh : (val I : {set S}) = val (bottom d) := eq_trans (esym hImage) hi.
have hn := proper_neq hI; by rewrite hh eqxx in hn.
Qed.

Definition prepend_extension : extension c (prepend hI) f.
Proof.
refine (@Build_extension S F c (prepend hI) P Q f
  (extended_selector hI prefix_index_positive) (carrier a) (acting_sub a) _
  (extension_map a) (extension_allowed a) (on_acting a) _).
- rewrite extended_index_last; exact: chain_sub.
- move=> i; case: (unliftP ord0 i)=> [j ->|->].
  + rewrite extended_index_lift /subgroup prepend_entry_lift; exact: entry_images.
  + rewrite extended_index_zero /subgroup prepend_entry_zero; exact hImage.
Defined.
End Extensions.

Section Deletion.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : {group S}.
Variable c : chain F.
Variable I : DPFusionOrbit.centric_object F.
Hypothesis hI : val I \proper val (bottom c).

Definition deletion_extension : extension (prepend hI) c (DPFusion.identity P).
Proof.
pose a := identity_extension P c.
refine (@Build_extension S F (prepend hI) c P P (DPFusion.identity P)
  (deletion_selector hI) (carrier a) (acting_sub a) _
  (extension_map a) (extension_allowed a) (on_acting a) _).
- rewrite deletion_index /subgroup prepend_entry_lift.
  have h := chain_sub a; by rewrite identity_index in h.
- move=> i; rewrite deletion_index /subgroup prepend_entry_lift.
  have h := entry_images a i; by rewrite identity_index in h.
Defined.
End Deletion.

Section Pointed.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : DPFusionOrbit.centric_object F.
Local Notation CP := (DPNormalizerOrbitCommaImage.pointed_category P).
Local Notation PC := (DPNormalizerOrbitPair.pair_category F).
Local Notation OC := (DPFusionOrbit.centric_orbit_category F).
Variable X : CP.
Let A := DPNormalizerOrbitCommaImage.pointed_pair X.
Let c := DPNormalizerOrbitPair.chain_of A.
Variable I : DPFusionOrbit.centric_object F.
Hypothesis hI : val I \proper val (bottom c).
Hypothesis hN : val (DPNormalizerOrbitPair.acting A) \subset 'N(val I).

Lemma prepend_normalizes :
  val (DPNormalizerOrbitPair.acting A) \subset DPNormalizerChain.normalizer (prepend hI).
Proof.
apply/subsetP=> x hx; apply/DPNormalizerChain.normalizerP=> i.
case: (unliftP ord0 i)=> [j ->|->].
- rewrite /subgroup prepend_entry_lift.
  exact (subsetP (@DPNormalizerChain.normalizer_sub S F c j) _
    (subsetP (DPNormalizerOrbitPair.acting_normalizes A) _ hx)).
- rewrite /subgroup prepend_entry_zero; exact: subsetP hN _ hx.
Qed.

Definition prepend_pair : PC :=
  Sub (DPNormalizerOrbitPair.acting A, prepend hI) prepend_normalizes.

Definition prepend_point : CP :=
  @DPNormalizerOrbitCommaImage.Build_pointed_object S F P prepend_pair
    (DPNormalizerOrbitCommaImage.pointed_iso X).

Definition prepend_deletion : hom CP prepend_point X.
Proof.
pose k := @DPNormalizerOrbitPair.hom_of_extension S F prepend_pair A
  (DPFusionSystem.arrow_identity F (val (DPNormalizerOrbitPair.acting A)))
  (deletion_extension (val (DPNormalizerOrbitPair.acting A)) hI).
refine (@Build_costructured_hom (opposite PC) (opposite OC)
  (functor_op (DPNormalizerOrbitPair.forget F)) P
  (DPNormalizerOrbitCommaImage.pointed_under X)
  (DPNormalizerOrbitCommaImage.pointed_under prepend_point) k _).
change (@Category.compose OC P (DPNormalizerOrbitPair.acting A) (DPNormalizerOrbitPair.acting A)
  (iso_hom (DPNormalizerOrbitCommaImage.pointed_iso X))
  (@Category.identity OC (DPNormalizerOrbitPair.acting A)) =
  iso_hom (DPNormalizerOrbitCommaImage.pointed_iso X)).
exact: Category.compose_id_right.
Defined.
End Pointed.
End DPNormalizerPointedChainPrefixExtensions.
