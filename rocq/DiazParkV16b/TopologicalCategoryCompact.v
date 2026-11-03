From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import topology subtype_topology.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module DPTopologicalCompact.

(** Compactness of an actual subset is compactness of its entire subtype space.
    This proof uses the actual initial topology, not a new compactness premise. *)
Lemma compact_subtype {X : topologicalType} (A : set X) :
  compact A -> @compact [the topologicalType of set_type A] setT.
Proof.
move=> hA F FF _.
have hFA : (@set_val X A @ F) A.
  change (F [set z : set_type A | A (set_val z)]).
  apply: filterS (filterT : F setT) => z _; exact: set_valP.
have [x [hx hcluster]] := hA (set_val @ F) _ hFA.
exists (exist _ x (mem_set hx)); split => //.
move=> B U hB [_ [[W hW <-] hxW hsub]].
have hB' : (set_val @ F) (set_val @` B).
  change (F [set z : set_type A | (set_val @` B) (set_val z)]).
  apply: filterS hB => z hz; by exists z.
have hxW' : nbhs x W := open_nbhs_nbhs (conj hW hxW).
have [y [[z hz hzy] hyW]] := hcluster _ _ hB' hxW'.
exists z; split => //; apply: hsub.
by rewrite /= hzy.
Qed.

End DPTopologicalCompact.
