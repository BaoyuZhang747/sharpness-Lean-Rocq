(** The image construction is an actual right adjoint to the inclusion of
    pointed normalizer pairs.  All functor and triangle equations are proved. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryComma CategoryAdjunction FusionSystems FusionOrbit.
From DiazParkV16b Require Import NormalizerOrbitCommaImageObjects NormalizerOrbitCommaImageUniversal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPNormalizerOrbitCommaImage DPNormalizerOrbitCommaImageUniversal.

Module DPNormalizerOrbitCommaImageCoreflection.
Section Coreflection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : centric_object F.
Local Notation UC := (under_category P).
Local Notation PT := (pointed_category P).

Definition image_functor : functor UC PT.
Proof.
refine (@Build_functor UC PT (@image_point S F P)
  (fun X Y f => image_lift (Category.compose (image_deletion X) f)) _ _).
- intro X; apply pointed_source_hom_unique.
- intros; apply pointed_source_hom_unique.
Defined.

Definition image_unit : nat_trans (functor_id PT) (functor_comp (pointed_inclusion P) image_functor).
Proof.
refine (@Build_nat_trans PT PT (functor_id PT) (functor_comp (pointed_inclusion P) image_functor)
  (fun Y => image_lift (Category.identity (pointed_under Y))) _).
intros; apply pointed_source_hom_unique.
Defined.

Definition image_counit : nat_trans (functor_comp image_functor (pointed_inclusion P)) (functor_id UC).
Proof.
refine (@Build_nat_trans UC UC (functor_comp image_functor (pointed_inclusion P)) (functor_id UC)
  (@image_deletion S F P) _).
intros; apply pointed_source_hom_unique.
Defined.

Definition image_adjunction : adjunction (pointed_inclusion P) image_functor.
Proof.
refine (@Build_adjunction PT UC (pointed_inclusion P) image_functor image_unit image_counit _ _).
- intro X; apply pointed_source_hom_unique.
- intro X; apply pointed_source_hom_unique.
Defined.
End Coreflection.
End DPNormalizerOrbitCommaImageCoreflection.

Print Assumptions DPNormalizerOrbitCommaImageCoreflection.image_adjunction.
