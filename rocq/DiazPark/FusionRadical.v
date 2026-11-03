From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionSystems FusionSaturation FusionOuterAutomorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionRadical.
Section Radical.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.

(** The standard condition on the actual finite outer automorphism group. *)
Definition radical (P : {group S}) : bool :=
  'O_p(DPFusionOuter.outer_group F P) == 1.

Theorem radical_normal_p_sub_inner (P : {group S}) (K : {group {perm S}}) :
  radical P -> p.-group K -> K <| DPFusionSaturation.aut_group F P ->
  K \subset DPFusionOuter.inner P.
Proof.
move=> /eqP hP pK nK.
have nbar : K / DPFusionOuter.inner P <| DPFusionOuter.outer_group F P.
  exact: morphim_normal.
have pbar : p.-group (K / DPFusionOuter.inner P) := quotient_pgroup _ pK.
have small := pcore_max pbar nbar.
rewrite hP in small.
apply/subsetP=> a Ka.
have aA := subsetP (normal_sub nK) a Ka.
have aN := subsetP (normal_norm (DPFusionOuter.inner_normal F P)) a aA.
apply: coset_idr aN _; apply/set1P.
apply: (subsetP small); exact: mem_quotient _ Ka.
Qed.
End Radical.
End DPFusionRadical.

Print Assumptions DPFusionRadical.radical_normal_p_sub_inner.
