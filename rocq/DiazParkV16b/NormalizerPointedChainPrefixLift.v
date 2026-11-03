(** Actual lifting through strict prefix insertion when the first image is prescribed. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryComma FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainExtensions NormalizerOrbitPairCategory
  NormalizerOrbitCommaImageObjects NormalizerOrbitPointedFirst NormalizerPointedSubgroups
  NormalizerPointedSubgroupObjectEquality NormalizerPointedChainPrefix NormalizerPointedChainPrefixExtensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerPointedChainPrefix DPNormalizerPointedChainPrefixExtensions.
Local Open Scope group_scope.

Module DPNormalizerPointedChainPrefixLift.
Section Lift.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : DPFusionOrbit.centric_object F.
Local Notation CP := (DPNormalizerOrbitCommaImage.pointed_category P).
Local Notation PC := (DPNormalizerOrbitPair.pair_category F).
Local Notation OC := (DPFusionOrbit.centric_orbit_category F).
Variables Y X : CP.
Let A := DPNormalizerOrbitCommaImage.pointed_pair Y.
Let B := DPNormalizerOrbitCommaImage.pointed_pair X.
Variable f : hom CP Y X.
Variable I : DPFusionOrbit.centric_object F.
Hypothesis hI : val I \proper val (bottom (DPNormalizerOrbitPair.chain_of B)).
Hypothesis hN : val (DPNormalizerOrbitPair.acting B) \subset 'N(val I).
Variable g : DPFusionSystem.arrow F (val (DPNormalizerOrbitPair.acting A)) (val (DPNormalizerOrbitPair.acting B)).
Hypothesis hg : DPFusionOrbit.orbit_class g = val (costructured_map f).
Variable a : DPNormalizerChainExtensions.extension (DPNormalizerOrbitPair.chain_of A)
  (DPNormalizerOrbitPair.chain_of B) (val g).
Hypothesis hImage : DPFusion.map_morphism (DPNormalizerChainExtensions.extension_map a) @*
  val (bottom (DPNormalizerOrbitPair.chain_of A)) = val I.

Definition lift_pair : hom PC A (prepend_pair hI hN).
Proof.
apply: (Sub (val (costructured_map f))); apply/asboolP.
exists g; split; first exact hg.
constructor; exact (@prepend_extension S F (DPNormalizerOrbitPair.chain_of A) (DPNormalizerOrbitPair.chain_of B) (val (DPNormalizerOrbitPair.acting A)) (val (DPNormalizerOrbitPair.acting B)) (val g) a I hI hImage).
Defined.

Definition prepend_lift : hom CP Y (prepend_point hI hN).
Proof.
refine (@Build_costructured_hom (opposite PC) (opposite OC)
  (functor_op (DPNormalizerOrbitPair.forget F)) P
  (DPNormalizerOrbitCommaImage.pointed_under (prepend_point hI hN))
  (DPNormalizerOrbitCommaImage.pointed_under Y) lift_pair _).
exact (costructured_commutes f).
Defined.

Lemma prepend_lift_deletion :
  Category.compose prepend_lift (prepend_deletion hI hN) = f.
Proof. exact: DPNormalizerOrbitCommaImage.pointed_source_hom_unique. Qed.
End Lift.

Section First.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : DPFusionOrbit.centric_object F.
Variable X : DPNormalizerOrbitCommaImage.pointed_category P.
Let B := DPNormalizerOrbitCommaImage.pointed_pair X.
Variable I : DPFusionOrbit.centric_object F.
Hypothesis hI : val I \proper val (bottom (DPNormalizerOrbitPair.chain_of B)).
Hypothesis hN : val (DPNormalizerOrbitPair.acting B) \subset 'N(val I).

Lemma first_prepend : DPNormalizerOrbitPointedFirst.first_object (prepend_point hI hN) =
  @DPNormalizerPointedSubgroups.Build_object S F P (DPNormalizerOrbitPair.acting B)
    (DPNormalizerOrbitCommaImage.pointed_iso X) (val I) (valP I) hN.
Proof.
apply DPNormalizerPointedSubgroupObjectEquality.fixed_point_object_eq.
apply congr1; exact: prepend_bottom.
Qed.
End First.
End DPNormalizerPointedChainPrefixLift.

