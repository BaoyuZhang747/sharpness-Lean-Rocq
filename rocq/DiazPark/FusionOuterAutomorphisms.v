From mathcomp Require Import all_ssreflect all_fingroup quotient pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionAutomorphisms.
Import DPFusion DPFusionAutomorphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionOuter.
Section Inner.
Variable S : finGroupType.
Variable P : {group S}.

Definition inner : {group {perm S}} := (conj_aut P @* P)%G.

Lemma inner_sub_Aut : inner \subset Aut P.
Proof. exact: Aut_conj_aut. Qed.

Lemma conjugate_conj_aut (a : {perm S}) (x : S) :
  a \in Aut P -> x \in P -> (conj_aut P x) ^ a = conj_aut P (a x).
Proof.
move=> Aa Px.
have Aax : a x \in P := Aut_closed Aa Px.
have Acx : conj_aut P x \in Aut P := Aut_aut _ _.
have Aci : a^-1 \in Aut P by rewrite groupV.
apply: (eq_Aut (groupJ Acx Aa) (Aut_aut _ _))=> y Py.
have Aiy : a^-1 y \in P := Aut_closed Aci Py.
rewrite /conjg !permM !norm_conj_autE ?(subsetP (normG P) _ Px)
  ?(subsetP (normG P) _ Aax) //.
have h := morphJ (autm Aa) Aiy Px.
change (a ((a^-1 y) ^ x) = (a (a^-1 y)) ^ (a x)) in h.
by rewrite permKV in h.
Qed.

Lemma inner_normal_Aut : inner <| [Aut P]%G.
Proof.
apply/andP; split; first exact: inner_sub_Aut.
apply/subsetP=> a Aa; rewrite inE; apply/subsetP=> b /imsetP[c /morphimP[x _ Px ->] ->].
rewrite conjugate_conj_aut //.
apply: mem_morphim; first exact: subsetP (normG P) _ (Aut_closed Aa Px).
exact: (Aut_closed Aa Px).
Qed.

End Inner.

Section FusionOuter.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : {group S}.

Lemma inner_sub : inner P \subset DPFusionSaturation.aut_group F P.
Proof.
apply: subset_trans (DPFusionSaturation.ambient_aut_sub F P).
exact: morphimS _ (normG P).
Qed.

Lemma inner_normal : inner P <| DPFusionSaturation.aut_group F P.
Proof.
apply/andP; split; first exact: inner_sub.
exact: subset_trans (DPFusionSaturation.aut_group_sub F P) (normal_norm (inner_normal_Aut P)).
Qed.

Definition outer_group : {group coset_of (inner P)} :=
  (DPFusionSaturation.aut_group F P / inner P)%G.

Definition ambient_outer_group : {group coset_of (inner P)} :=
  (DPFusionSaturation.ambient_aut_group P / inner P)%G.

Lemma ambient_outer_sub : ambient_outer_group \subset outer_group.
Proof. exact: quotientS (DPFusionSaturation.ambient_aut_sub F P). Qed.

Lemma ambient_outer_sylow p (sat : DPFusionSaturation.saturated F p) :
  DPFusionSystem.fully_normalized F P -> p.-Sylow(outer_group) ambient_outer_group.
Proof.
move=> hP; have [_ syl] := DPFusionSaturation.saturation_fully_normalized sat hP.
exact: (morphim_pSylow (coset (inner P))
  (subset_trans (DPFusionSaturation.ambient_aut_sub F P) (normal_norm inner_normal)) syl).
Qed.

End FusionOuter.
End DPFusionOuter.


