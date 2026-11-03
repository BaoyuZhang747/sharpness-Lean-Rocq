From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  HomologicalModuleIso MackeyModuleCarriers FusionSystems FusionOrbit FusionMackeyShape
  MackeyStructures MackeyPair.
From DiazParkV29 Require Import SimpleTraceSummands SimpleTransportedTrace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPFusionMackey DPSimpleTraceSummands
  DPSimpleTransportedTrace DiazParkHomologicalModuleIso.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPSimpleChoiceComparison.
Section ChangeFusionIsomorphism.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_module R (fusion_mackey_shape F).
Variables Q L U : {group S}.
Variables alpha beta : @isomorphism (orbit_category F) Q L.

Lemma trace_transport_inverse_value (w : trace_summand (pair_of_mackey M) L U) :
    submodule_val (module_hom_fun (iso_inv (@transported_trace_iso S F R M Q L U beta)) w) =
    mackey_push M (iso_inv beta) (submodule_val w).
Proof.
have he := module_iso_inv_hom_apply (@transported_trace_iso S F R M Q L U beta) w.
have hv := congr1 (@submodule_val R (mackey_value M L) (trace_image (pair_of_mackey M) L U)) he.
change (mackey_push M (iso_hom beta)
  (submodule_val (module_hom_fun (iso_inv (@transported_trace_iso S F R M Q L U beta)) w)) =
  submodule_val w) in hv.
have hb := congr1 (mackey_push M (iso_inv beta)) hv.
by rewrite mackey_push_iso_cancel in hb.
Qed.

Definition trace_choice_iso :
    @isomorphism (module_category R)
      (@transported_trace_summand S F R M Q L U alpha)
      (@transported_trace_summand S F R M Q L U beta) :=
  module_iso_comp (@transported_trace_iso S F R M Q L U alpha)
    (iso_symm (@transported_trace_iso S F R M Q L U beta)).

Theorem trace_choice_iso_formula (v : @transported_trace_summand S F R M Q L U alpha) :
    submodule_val (module_hom_fun (iso_hom trace_choice_iso) v) =
    mackey_push M (compose (iso_hom alpha) (iso_inv beta)) (submodule_val v).
Proof.
change (submodule_val (module_hom_fun (iso_inv (@transported_trace_iso S F R M Q L U beta))
  (module_hom_fun (iso_hom (@transported_trace_iso S F R M Q L U alpha)) v)) =
  mackey_push M (compose (iso_hom alpha) (iso_inv beta)) (submodule_val v)).
rewrite trace_transport_inverse_value.
change (mackey_push M (iso_inv beta) (mackey_push M (iso_hom alpha) (submodule_val v)) =
  mackey_push M (compose (iso_hom alpha) (iso_inv beta)) (submodule_val v)).
by rewrite mackey_push_comp.
Qed.
End ChangeFusionIsomorphism.
End DPSimpleChoiceComparison.
