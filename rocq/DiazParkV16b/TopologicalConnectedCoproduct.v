(** A continuous map from a nonempty connected space into an actual disjoint union
    factors continuously through its unique component. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import topology sigT_topology unstable.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCoproductHomotopy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalCoproductHomotopy.
Local Open Scope classical_set_scope.

Module DPTopologicalConnectedCoproduct.
Section Connected.
Variables (I : choiceType) (X : I -> topologicalType).

Lemma family_index_set_open (S : set I) :
  @open (family_space X) (fun z => S (projT1 z)).
Proof.
apply/sigT_openP => i.
case: (pselect (S i)) => hi.
- have e : (existT X i @^-1` (fun z => S (projT1 z))) = setT.
    by apply/seteqP; split=> x _.
  rewrite e; exact: openT.
- have e : (existT X i @^-1` (fun z => S (projT1 z))) = set0.
    by apply/seteqP; split=> x // hx; exfalso; exact: hi hx.
  rewrite e; exact: open0.
Qed.

Lemma family_index_set_closed (S : set I) :
  @closed (family_space X) (fun z => S (projT1 z)).
Proof.
have e : (fun z : family_space X => S (projT1 z)) =
    ~` (fun z => (~` S) (projT1 z)).
  apply/seteqP; split=> z hz.
  - by move=> hn; exact: hn hz.
  - apply: contrapT hz; exact.
rewrite e; apply: open_closedC; exact: family_index_set_open.
Qed.

Variables (Z : topologicalType) (z0 : Z).
Variable hZ : @connected Z setT.
Variable f : continuousType Z (family_space X).

Definition connected_family_index : I := projT1 (f z0).

Lemma connected_family_index_constant z : projT1 (f z) = connected_family_index.
Proof.
pose S : set (family_space X) := fun w => projT1 w = connected_family_index.
pose B : set Z := f @^-1` S.
have ho : open B.
  apply: (proj1 (continuousP f) (@cts_fun _ _ f)).
  change (@open (family_space X) (fun z => projT1 z = connected_family_index)).
  exact (@family_index_set_open (fun i : I => i = connected_family_index)).
have hc : closed B.
  apply: preimage_closed; last exact: (@family_index_set_closed (fun i : I => i = connected_family_index)).
  by move=> w _; exact: cts_fun.
have e : B = setT.
  apply: hZ.
  - by exists z0.
  - exists B => //; by rewrite setTI.
  - exists B => //; by rewrite setTI.
have : B z by rewrite e.
exact.
Qed.

Lemma connected_family_factor_exists z :
  exists a : X connected_family_index, existT X connected_family_index a = f z.
Proof.
have h := connected_family_index_constant z.
case: (f z) h => i a /= h; subst i; by exists a.
Qed.

Definition connected_family_factor_fun z : X connected_family_index :=
  proj1_sig (constructive_indefinite_description (connected_family_factor_exists z)).

Lemma connected_family_factor_equation z :
  existT X connected_family_index (connected_family_factor_fun z) = f z.
Proof. exact: (proj2_sig (constructive_indefinite_description (connected_family_factor_exists z))). Qed.

Lemma connected_family_factor_continuous : continuous connected_family_factor_fun.
Proof.
apply/continuousP => U hU.
have e : connected_family_factor_fun @^-1` U =
    f @^-1` (existT X connected_family_index @` U).
  apply/seteqP; split=> z hz.
  - exists (connected_family_factor_fun z) => //; exact: connected_family_factor_equation.
  - have [a ha ea] := hz.
    have eq : a = connected_family_factor_fun z.
      apply: (@existT_inj2 I X connected_family_index).
      rewrite connected_family_factor_equation; exact: ea.
    change (U (connected_family_factor_fun z)); by rewrite -eq.
rewrite e; apply: (proj1 (continuousP f) (@cts_fun _ _ f)).
exact: existT_open_map.
Qed.

Definition connected_family_factor : continuousType Z (X connected_family_index) :=
  continuous_map connected_family_factor_continuous.

End Connected.
End DPTopologicalConnectedCoproduct.
