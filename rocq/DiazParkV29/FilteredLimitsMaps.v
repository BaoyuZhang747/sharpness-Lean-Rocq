(** Functoriality and finite-coordinate properties of the constructed colimit. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import CategoryModules CategoryModuleLinear.
From DiazParkV29 Require Import FilteredLimitsDirected.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFilteredLimits.
Local Open Scope ring_scope.

Module DPFilteredMaps.

Section Map.
Variable R : pzRingType.
Variable I : directed_poset.
Variables U V : directed_module R I.
Variable a : forall i, {linear dm_value U i -> dm_value V i}.
Hypothesis natural : forall i j (h : stage_le i j) x,
  a j (dm_map U h x) = dm_map V h (a i x).

Definition map_leg i : {linear dm_value U i -> colimit_module V} :=
  (@colimit_in R I V i \o a i : {linear dm_value U i -> colimit_module V}).
Lemma map_leg_natural i j (h : stage_le i j) x : map_leg j (dm_map U h x) = map_leg i x.
Proof. rewrite /map_leg /= natural; exact: colimit_in_map. Qed.

Definition direct_limit_map : colimit_module U -> colimit_module V :=
  colimit_lift map_leg.
Lemma direct_limit_map_in i (x : dm_value U i) :
    direct_limit_map (colimit_in x) = colimit_in (a i x).
Proof. apply colimit_lift_in; exact: map_leg_natural. Qed.
Lemma direct_limit_map_linear : linear direct_limit_map.
Proof. apply colimit_lift_linear; exact: map_leg_natural. Qed.
HB.instance Definition _ := GRing.isLinear.Build R (colimit_module U) (colimit_module V) _
  direct_limit_map direct_limit_map_linear.
End Map.

Section FiniteBounds.
Variable I : directed_poset.
Definition classical_stage := classicType (stage I).
HB.instance Definition _ := Choice.on classical_stage.

Fixpoint upper_list (s : seq classical_stage) : stage I :=
  match s with
  | [::] => stage_base I
  | i :: t => upper i (upper_list t)
  end.
Lemma upper_list_bound (s : seq classical_stage) (i : classical_stage) :
  i \in s -> stage_le i (upper_list s).
Proof.
elim: s => [|j s ih] /=; first by rewrite in_nil.
rewrite in_cons => /orP [/eqP -> | hi].
- exact: le_upper_l.
- exact (stage_trans (ih hi) (le_upper_r j (upper_list s))).
Qed.

Lemma finite_upper (T : finType) (f : T -> stage I) :
    exists k, forall t, stage_le (f t) k.
Proof.
exists (upper_list [seq f t | t <- enum T]); move=> t.
apply upper_list_bound; apply map_f; exact: mem_enum.
Qed.
End FiniteBounds.

Section FiniteLifts.
Variable R : pzRingType.
Variable I : directed_poset.
Variable T : finType.
Variable V : T -> directed_module R I.

Theorem finite_colimit_representatives (x : forall t, colimit_module (V t)) :
    exists i (v : forall t, dm_value (V t) i),
      forall t, colimit_in (v t) = x t.
Proof.
pose reps t := constructive_indefinite_description (colimit_in_surjective (x t)).
pose ix t := proj1_sig (reps t).
pose vals t := constructive_indefinite_description (proj2_sig (reps t)).
have [i hi] := finite_upper ix.
exists i, (fun t => dm_map (V t) (hi t) (proj1_sig (vals t))).
move=> t; rewrite colimit_in_map; exact: (proj2_sig (vals t)).
Qed.

Theorem finite_colimit_eventual_zero i (x : forall t, dm_value (V t) i)
    (hx : forall t, colimit_in (x t) = 0) :
    exists j (h : stage_le i j), forall t, dm_map (V t) h (x t) = 0.
Proof.
pose witnesses t := constructive_indefinite_description (proj1 (colimit_in_zero (x t)) (hx t)).
pose ix t := proj1_sig (witnesses t).
have [k hk] := finite_upper ix.
pose j := upper i k.
have hij : stage_le i j := le_upper_l i k.
have hkj : stage_le k j := le_upper_r i k.
exists j, hij; move=> t.
have [hit he] := proj2_sig (witnesses t).
have h : stage_le (ix t) j := stage_trans (hk t) hkj.
rewrite (dm_proof_irrelevance (V := V t) hij (stage_trans hit h)) -dm_comp he linear0.
reflexivity.
Qed.
End FiniteLifts.
End DPFilteredMaps.
