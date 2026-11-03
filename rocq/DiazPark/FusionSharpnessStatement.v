(** The manuscript's sharpness assertion, for actual full Mackey modules
    and independently constructed right derived inverse limits. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  FusionSystems FusionOrbit FusionMackeyShape MackeyStructures MackeyBarReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module DPFusionSharpness.
Definition sharpness (R : comPzRingType) (S : finGroupType)
    (F : DPFusionSystem.system S) : Prop :=
  forall M : mackey_module R (DPFusionMackey.fusion_mackey_shape F),
    forall n (q : derived_limit R
      (mackey_codiagram (DPFusionOrbit.centric_inclusion F) M) n.+1), q = 0.
End DPFusionSharpness.
