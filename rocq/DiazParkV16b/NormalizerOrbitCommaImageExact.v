(** The literal image adjunction transports pointed-chain exactness to the
    actual structured comma.  Pointed-chain exactness is supplied separately. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import NormalizerOrbitCommaImageObjects
  NormalizerOrbitCommaImageCoreflection CategoryStringExactnessTransport CategoryInducedBarCofinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPNormalizerOrbitCommaImageExact.
Theorem under_exact_of_pointed (S : finGroupType) (F : DPFusionSystem.system S)
    (P : DPFusionOrbit.centric_object F) (R : pzRingType) :
  category_string_augmented_exact R (DPNormalizerOrbitCommaImage.pointed_category P) ->
  category_string_augmented_exact R (DPNormalizerOrbitCommaImage.under_category P).
Proof.
exact (@DPCategoryStringExactnessTransport.exact_right_of_adjunction R
  (DPNormalizerOrbitCommaImage.under_category P) (DPNormalizerOrbitCommaImage.pointed_category P)
  (DPNormalizerOrbitCommaImageCoreflection.image_functor P)
  (DPNormalizerOrbitCommaImage.pointed_inclusion P)
  (DPNormalizerOrbitCommaImageCoreflection.image_adjunction P)).
Qed.
End DPNormalizerOrbitCommaImageExact.
