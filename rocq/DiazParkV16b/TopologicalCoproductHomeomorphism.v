(** Actual sigma-family homeomorphisms and T1 separation. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology sigT_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCoproductHomotopy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalCoproductHomotopy.
Local Open Scope classical_set_scope.

Module DPTopologicalCoproductHomeomorphism.
Section Homeomorphism.
Variable I : choiceType.
Variables X Y : I -> topologicalType.
Variable e : forall i, homeomorphism (X i) (Y i).
Definition family_homeomorphism : homeomorphism (family_space X) (family_space Y).
Proof.
refine (@Build_isomorphism topological_category _ _
  (family_map (fun i => iso_hom (e i))) (family_map (fun i => iso_inv (e i))) _ _).
- apply: topological_hom_ext => [[i x]].
  change (existT X i (iso_inv (e i) (iso_hom (e i) x)) = existT X i x).
  by rewrite homeomorphism_forwardK.
- apply: topological_hom_ext => [[i y]].
  change (existT Y i (iso_hom (e i) (iso_inv (e i) y)) = existT Y i y).
  by rewrite homeomorphism_inverseK.
Defined.
Lemma family_homeomorphism_at i x :
  iso_hom family_homeomorphism (existT X i x) = existT Y i (iso_hom (e i) x).
Proof. reflexivity. Qed.
End Homeomorphism.

Section Separation.
Variable I : choiceType.
Variable X : I -> topologicalType.
Variable hX : forall i, accessible_space (X i).

Lemma family_closed_singleton (z : family_space X) : closed [set z].
Proof.
case: z => i x; rewrite -openC; apply/sigT_openP => j.
case: (eqVneq j i) => [->|hne].
- have e : existT X i @^-1` (~` [set existT X i x]) = ~` [set x].
    apply/seteqP; split=> y hy.
    * move=> ey; apply hy; exact (congr1 (existT X i) ey).
    * move=> ey; apply hy; exact (existT_inj2 ey).
  rewrite e openC; exact (@accessible_closed_set1 (X i) (@hX i) x).
- have e : existT X j @^-1` (~` [set existT X i x]) = setT.
    apply/seteqP; split=> y; first by [].
    move=> _ ey; have ej : j = i := congr1 (@projT1 _ X) ey.
    by move: hne; rewrite ej eqxx.
  rewrite e; exact: openT.
Qed.

Theorem family_accessible : accessible_space (family_space X).
Proof.
move=> x y hxy; exists (~` [set y]); rewrite !inE /=; split.
- rewrite openC; exact: family_closed_singleton.
- exact/eqP.
- by [].
Qed.
End Separation.
End DPTopologicalCoproductHomeomorphism.
