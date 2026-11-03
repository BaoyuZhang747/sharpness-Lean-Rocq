(** The ordinary p-subgroup reflector, including the fixed-Sylow version.
    The latter actually works below any subgroup containing the normal p-group. *)
From mathcomp Require Import all_boot all_fingroup pgroup sylow.
From DiazPark Require Import Category CategoryAdjunction GroupOrbitCollections
  GroupOrbitNormalReflection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPGroupOrbitP.
Section POrbit.
Variable G : finGroupType.
Variable p : nat.
Definition psubgroups (H : {group G}) := p.-group H.
Definition orbit_category := DPGroupOrbitCollection.category psubgroups.
Variable N : {group G}.
Hypothesis normalN : N <| [set: G].
Hypothesis pN : p.-group N.

Lemma join_pgroup H : psubgroups H -> psubgroups (DPGroupOrbitNormal.join N H).
Proof.
  move=> pH. change (is_true (p.-group H)) in pH.
  change (is_true (p.-group (H <*> N))). rewrite norm_joinEl.
  by rewrite pgroupM pH pN.
  exact (subset_trans (subsetT H) (normal_norm normalN)).
Qed.

Definition reflector := DPGroupOrbitNormal.reflector normalN join_pgroup.
Definition inclusion := DPGroupOrbitNormal.inclusion N psubgroups.
Definition normal_p_reflection : adjunction reflector inclusion :=
  DPGroupOrbitNormal.normal_reflection normalN join_pgroup.

Variable T : {group G}.
Hypothesis sNT : N \subset T.
Definition bounded_psubgroups (H : {group G}) := p.-group H && (H \subset T).
Definition bounded_orbit_category := DPGroupOrbitCollection.category bounded_psubgroups.
Lemma join_bounded H : bounded_psubgroups H ->
    bounded_psubgroups (DPGroupOrbitNormal.join N H).
Proof.
  move/andP=> [pH hH]. apply/andP; split; first exact (join_pgroup pH).
  change (H <*> N \subset T). rewrite join_subG. exact/andP.
Qed.
Definition bounded_reflector := DPGroupOrbitNormal.reflector normalN join_bounded.
Definition bounded_inclusion := DPGroupOrbitNormal.inclusion N bounded_psubgroups.
Definition bounded_normal_p_reflection : adjunction bounded_reflector bounded_inclusion :=
  DPGroupOrbitNormal.normal_reflection normalN join_bounded.

End POrbit.

Lemma normal_p_sub_sylow (G : finGroupType) (p : nat) (N T : {group G}) :
    N <| [set: G] -> p.-group N -> p.-Sylow([set: G]) T -> N \subset T.
Proof. move=> hN pN hT. exact (normal_sub_max_pgroup (Hall_max hT) pN hN). Qed.

End DPGroupOrbitP.
