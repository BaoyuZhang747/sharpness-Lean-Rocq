(** Each actual factor in the finite series is the named simple Mackey
    functor S_(Q,T(Q)), with all maps, not merely its objectwise dimensions. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import MackeyStructures MackeyFusionMinimal
  FusionSystems FusionMackeyShape.
From DiazParkV29 Require Import CompositionSeries CompositionReduction
  SimpleMackeyTransport SimpleFunctor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCompositionSeries DPCompositionReduction.

Module DPCompositionIdentification.
Section Factors.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable K : fieldType.
Variable M : mackey_module K (DPFusionMackey.fusion_mackey_shape F).
Variable s : composition_series M.
Variable T : mackey_module K (DPFusionMackey.fusion_mackey_shape F).
Hypothesis hT : factor_of_series s T.
Variable Q : {group S}.
Hypothesis minimalQ : DPMackeyMinimal.subgroup_minimal T Q.

Definition factor_simple := factor_of_series_simple hT.
Definition identified_factor := @DPSimpleFunctor.S_Q_MQ S F K T factor_simple Q minimalQ.

Definition factor_identification :
    DPSimpleMackeyTransport.mackey_isomorphism T identified_factor :=
  @DPSimpleFunctor.simple_functor_identification S F K T factor_simple Q minimalQ.

Theorem identified_factor_simple : mackey_simple identified_factor.
Proof. exact: DPSimpleFunctor.S_Q_MQ_simple. Qed.

End Factors.
End DPCompositionIdentification.

Check DPCompositionIdentification.factor_identification.
Print Assumptions DPCompositionIdentification.factor_identification.
