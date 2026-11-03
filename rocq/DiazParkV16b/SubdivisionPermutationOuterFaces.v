(** The outer permutation bijection uses the literal monotone coface. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From mathcomp Require Import all_ssreflect all_algebra all_fingroup.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators SimplexCategoryIdentities
  SubdivisionPermutationOuter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GroupScope DPSimplexCategory DPSimplexOperators DPSimplexIdentities DPSubdivisionPermutationOuter.

Module DPSubdivisionPermutationOuterFaces.

Lemma coface_is_lift n (i : 'I_n.+2) (k : 'I_n.+1) : coface i k = lift i k.
Proof.
apply val_inj; change (coface_value i k = bump i k).
rewrite /coface_value /bump.
have e : Nat.leb (val i) (val k) = (i <= k)%N.
  case h : (Nat.leb (val i) (val k)); symmetry.
  - apply/leP; exact: (proj1 (Nat.leb_le _ _) h).
  - apply/negbTE; rewrite -ltnNge; apply/ltP; exact: (proj1 (Nat.leb_gt _ _) h).
by rewrite e; case: (i <= k)%N.
Qed.

Lemma last_lift_is_widen n (k : 'I_n.+1) : lift ord_max k = vertex_widen k.
Proof. apply val_inj; change ((lift ord_max k : nat) = (k : nat)); exact: lift_max. Qed.

Lemma outer_assemble_coface n (i : 'I_n.+2) (q : {perm 'I_n.+1}) k :
  outer_assemble i q (vertex_widen k) = coface i (q k).
Proof. by rewrite -last_lift_is_widen outer_assemble_lift coface_is_lift. Qed.

Lemma outer_remove_coface n (p : {perm 'I_n.+2}) k :
  p (vertex_widen k) = coface (p ord_max) (outer_remove p k).
Proof. by rewrite -last_lift_is_widen coface_is_lift outer_remove_apply outer_remove_spec. Qed.
End DPSubdivisionPermutationOuterFaces.
