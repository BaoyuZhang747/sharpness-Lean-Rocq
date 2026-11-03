(** Actual image-prefix coreflection in the first-entry comma.  A proper
    image is inserted as a new first subgroup; a full image needs no insertion. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient pgroup boolp.
From DiazPark Require Import Category CategoryComma CategoryAdjunction FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import LinkingChainObjects NormalizerOrbitPairCategory NormalizerOrbitCommaImageObjects
  NormalizerOrbitPointedFirst NormalizerPointedSubgroups NormalizerPointedSubgroupImageFactorization
  NormalizerPointedSubgroupImageIsomorphisms NormalizerOrbitPointedFirstComma NormalizerOrbitPointedFirstImages
  NormalizerPointedChainPrefixExtensions NormalizerPointedChainPrefixLift NormalizerPointedSubgroupObjectEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerOrbitPointedFirstComma
  DPNormalizerPointedSubgroupImageFactorization DPNormalizerPointedSubgroupImageIsomorphisms
  DPNormalizerPointedChainPrefixExtensions DPNormalizerPointedChainPrefixLift.
Local Open Scope group_scope.

Module DPNormalizerOrbitPointedFirstCoreflection.
Section Coreflection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable P : DPFusionOrbit.centric_object F.
Local Notation CP := (DPNormalizerOrbitCommaImage.pointed_category P).
Local Notation SP := (DPNormalizerPointedSubgroups.pointed_category P).
Local Notation E := (DPNormalizerOrbitPointedFirst.first_functor P).
Variable B : SP.
Local Notation UC := (first_under B).
Local Notation PT := (first_points B).

Record image_prefix_data (X : UC) := {
  prefix_point : PT;
  prefix_deletion : hom UC (point_under prefix_point) X;
  prefix_lift : forall (Y : PT), hom UC (point_under Y) X -> hom PT Y prefix_point
}.

Definition full_image_data (X : UC)
    (he : arrow_image (costructured_arrow X) =
      DPNormalizerPointedSubgroups.subgroup (fobj E (costructured_source X))) : image_prefix_data X.
Proof.
pose U : PT := @Build_first_point S F P B (costructured_source X) (full_image_iso he).
refine (@Build_image_prefix_data X U _ _).
- refine (@Build_costructured_hom (opposite CP) (opposite SP) (functor_op E) B
    X (point_under U) (@Category.identity CP (costructured_source X)) _).
  exact (@DPNormalizerPointedSubgroups.hom_unique S F P B (fobj E (costructured_source X)) _ _).
- move=> Y f.
  refine (@Build_costructured_hom (opposite CP) (opposite SP) (functor_op E) B
    (point_under U) (point_under Y) (costructured_map f) _).
  exact (@DPNormalizerPointedSubgroups.hom_unique S F P B (fobj E (costructured_source X)) _ _).
Defined.

Section ProperImage.
Variable X : UC.
Let H := arrow_image (costructured_arrow X).
Let M := image_object (costructured_arrow X).
Let I : DPFusionOrbit.centric_object F :=
  Sub H (DPNormalizerPointedSubgroups.subgroup_centric M).
Let c := DPNormalizerOrbitPair.chain_of
  (DPNormalizerOrbitCommaImage.pointed_pair (costructured_source X)).
Hypothesis hI : H \proper val (bottom c).
Let hN := DPNormalizerPointedSubgroups.normalizes M.
Let Z := @prepend_point S F P (costructured_source X) I hI hN.

Lemma proper_first_image : fobj E Z = M.
Proof.
change (DPNormalizerOrbitPointedFirst.first_object Z = M).
rewrite (@first_prepend S F P (costructured_source X) I hI hN).
apply DPNormalizerPointedSubgroupObjectEquality.fixed_point_object_eq; reflexivity.
Qed.

Definition proper_first_iso : @isomorphism SP B (fobj E Z).
Proof. rewrite proper_first_image; exact (image_iso (costructured_arrow X)). Defined.

Definition proper_point : PT := @Build_first_point S F P B Z proper_first_iso.

Definition proper_deletion : hom UC (point_under proper_point) X.
Proof.
refine (@Build_costructured_hom (opposite CP) (opposite SP) (functor_op E) B
  X (point_under proper_point) (@prepend_deletion S F P (costructured_source X) I hI hN) _).
exact (@DPNormalizerPointedSubgroups.hom_unique S F P B (fobj E (costructured_source X)) _ _).
Defined.

Lemma proper_lift_exists (Y : PT) (f : hom UC (point_under Y) X) :
  exists k : hom PT Y proper_point, True.
Proof.
have [g [hg [a]]] := DPNormalizerOrbitPair.hom_compatible (costructured_map (costructured_map f)).
have hi := @DPNormalizerOrbitPointedFirstImages.first_carrier_image S F p pS sat P B Y X f g hg a.
pose k := @prepend_lift S F P (point_chain Y) (costructured_source X) (costructured_map f) I hI hN g hg a hi.
have hk : hom PT Y proper_point.
  refine (@Build_costructured_hom (opposite CP) (opposite SP) (functor_op E) B
    (point_under proper_point) (point_under Y) k _).
  exact (@DPNormalizerPointedSubgroups.hom_unique S F P B (fobj E Z) _ _).
exists hk; constructor.
Qed.

Definition proper_image_data : image_prefix_data X :=
  @Build_image_prefix_data X proper_point proper_deletion
    (fun Y f => proj1_sig (cid (proper_lift_exists f))).
End ProperImage.

Definition selected_data (X : UC) : image_prefix_data X.
Proof.
case: (boolP (arrow_image (costructured_arrow X) ==
  DPNormalizerPointedSubgroups.subgroup (fobj E (costructured_source X))))=> [/eqP he|hne].
- exact (full_image_data he).
- apply proper_image_data.
  rewrite properEneq arrow_image_sub andbT.
  apply/negP=> /eqP he; apply (negP hne); apply/eqP; exact: val_inj he.
Defined.

Definition first_coreflection : functor UC PT.
Proof.
refine (@Build_functor UC PT (fun X => prefix_point (selected_data X))
  (fun X Y f => prefix_lift (selected_data Y)
    (Category.compose (prefix_deletion (selected_data X)) f)) _ _).
- intros; apply first_under_hom_unique.
- intros; apply first_under_hom_unique.
Defined.

Definition first_unit : nat_trans (functor_id PT) (functor_comp (points_inclusion B) first_coreflection).
Proof.
refine (@Build_nat_trans PT PT (functor_id PT) (functor_comp (points_inclusion B) first_coreflection)
  (fun Y => prefix_lift (selected_data (point_under Y)) (@Category.identity UC (point_under Y))) _).
intros; apply first_under_hom_unique.
Defined.

Definition first_counit : nat_trans (functor_comp first_coreflection (points_inclusion B)) (functor_id UC).
Proof.
refine (@Build_nat_trans UC UC (functor_comp first_coreflection (points_inclusion B)) (functor_id UC)
  (fun X => prefix_deletion (selected_data X)) _).
intros; apply first_under_hom_unique.
Defined.

Definition first_coreflection_adjunction : adjunction (points_inclusion B) first_coreflection.
Proof.
refine (@Build_adjunction PT UC (points_inclusion B) first_coreflection first_unit first_counit _ _);
  intros; apply first_under_hom_unique.
Defined.
End Coreflection.
End DPNormalizerOrbitPointedFirstCoreflection.





