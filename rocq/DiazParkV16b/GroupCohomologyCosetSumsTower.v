(** The actual coset sum is transitive for nested subgroups. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazParkV16b Require Import GroupCohomologyTransferCosets
  GroupCohomologyCosetSumsTowerCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomologyTransferCosets DPGroupCohomologyCosetSums.
Local Open Scope ring_scope.
Local Open Scope group_scope.

Module DPGroupCohomologyCosetSumsTower.
Section Tower.
Variable G : finGroupType.
Variable V : zmodType.
Variables P Q T : {group G}.
Hypotheses (hPQ : P \subset Q) (hQT : Q \subset T).

Theorem coset_sum_tower (F : G -> V) (hF : left_invariant P F) :
  coset_sum P T F = coset_sum Q T (fun t => coset_sum P Q (fun q => F (q * t))).
Proof.
rewrite /coset_sum [LHS]big_sub.
rewrite (reindex (tower_map hPQ hQT)); last exact: onW_bij (tower_map_bijective hPQ hQT).
rewrite [RHS]big_sub.
transitivity (\sum_(v : coset_type Q T) \sum_(u : coset_type P Q)
  F (repr (val u) * repr (val v))%g).
- rewrite pair_bigA; apply: eq_bigr=> [[v u]] _.
  rewrite tower_map_value -{1}(coset_representative u) -rcosetM.
  exact (invariant_repr hF _).
- apply: eq_bigr=> v _; rewrite [RHS]big_sub; reflexivity.
Qed.

End Tower.
End DPGroupCohomologyCosetSumsTower.

Print Assumptions DPGroupCohomologyCosetSumsTower.coset_sum_tower.



