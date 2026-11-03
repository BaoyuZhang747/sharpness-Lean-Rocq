From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryLimits CategoryFinite
  CategoryFiniteSlice CategoryFiniteClasses FusionSystems FusionOrbit
  FusionFiniteCategory BurnsideFusionRanks BurnsideMarkDeterminant
  PrimeLocalRing PrimeLocalIntegers.
Import GRing.Theory DPPrimeLocal DiazParkBurnsideMarks DPBurnsideFusionRanks.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Lemma burnside_prime_local_charzero p :
    GRing.pchar [the idomainType of (DPPrimeLocal.type p : Type)] =i pred0.
Proof.
apply/(proj2 (GRing.pcharf0P _))=> n.
exact: DPPrimeLocalIntegers.natural_eq0.
Qed.

Section CentricSliceMarks.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : fc_object (DPFusionFinite.centric_finite_category F).
Variable p : nat.
Local Notation C := (@fc_slice (DPFusionFinite.centric_finite_category F) P).
Local Notation R := [the idomainType of (DPPrimeLocal.type p : Type)].

Theorem centric_slice_mark_determinant_nonzero :
    \det (burnside_mark_matrix C R) != 0.
Proof.
apply: (@burnside_mark_determinant_nonzero C R (@centric_slice_rank S F P)).
- move=> X Y f; exact: centric_slice_rank_le f.
- move=> X Y f h; exists (centric_slice_equal_rank_iso f h).
  exact: centric_slice_equal_rank_iso_hom.
- exact: burnside_prime_local_charzero.
Qed.

End CentricSliceMarks.

Print Assumptions burnside_prime_local_charzero.
Print Assumptions centric_slice_mark_determinant_nonzero.
