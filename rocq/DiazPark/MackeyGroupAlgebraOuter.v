From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import ModuleInfrastructure MackeyStructures MackeyMinimal
  MackeyFusionMinimal MackeyGroupAction MackeyGroupActionOuter
  MackeyGroupAlgebra MackeyGroupAlgebraModule MackeyGroupAlgebraSimple
  FusionSystems FusionOrbit FusionMackeyShape FusionOuterAutomorphisms
  FusionOuterEndomorphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOuter DPFusionOuterEndomorphisms DPMackeyOuterAction.
Local Open Scope ring_scope.

Module DPMackeyOuterModule.
Section ActualOuterModule.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_module R (DPFusionMackey.fusion_mackey_shape F).
Variable P : {group S}.

(** An actual module over the convolution group algebra of the actual
    quotient Aut_F(P)/Inn(P).  Inversion translates the manuscript's right
    action into the native left-module convention. *)
Definition outer_group_algebra_module :=
  group_algebra_module (outer_right_action M P).

Lemma outer_group_algebra_carrier : (outer_group_algebra_module : Type) = mackey_value M P.
Proof. reflexivity. Qed.

Lemma outer_group_algebra_action
    (g : [subg (outer_group F P)]) (x : outer_group_algebra_module) :
    group_basis R g^-1 *: x = mackey_push M (@outer_endomorphism S F P g) x.
Proof. exact: group_algebra_module_right_action. Qed.

Theorem outer_group_algebra_simple :
    automorphism_simple_at M P -> module_is_simple outer_group_algebra_module.
Proof.
move=> h; apply/(action_simple_group_algebra_iff (outer_right_action M P)).
exact: outer_action_simple.
Qed.

Theorem conjugate_outer_group_algebra_simple
    (Q : {group S}) (leastQ : mackey_least_nonzero M (fun U : {group S} => #|U|) Q)
    (hM : mackey_simple M) (conjQP : DPFusionSystem.conjugate F Q P) :
    module_is_simple outer_group_algebra_module.
Proof.
apply: outer_group_algebra_simple.
exact: (@DPMackeyMinimal.conjugate_automorphism_simple S F R M Q leastQ hM P conjQP).
Qed.

End ActualOuterModule.
End DPMackeyOuterModule.
