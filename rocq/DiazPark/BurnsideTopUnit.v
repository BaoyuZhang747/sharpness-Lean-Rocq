From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryFinite CategoryFiniteClasses
  CategoryFiniteProducts CategoryFiniteSlice CategoryFiniteSliceProducts
  FusionSystems FusionOrbit FusionFiniteCategory BurnsideFusionRanks
  BurnsideAlgebra BurnsideMarkAlgebra BurnsideTopElement BurnsidePrimeLocal
  PrimeLocalRing PrimeLocalIntegers.
Import GRing.Theory DPPrimeLocal DPBurnsideFusionRanks.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CentricTopUnit.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Local Notation C := (DPFusionFinite.centric_finite_category F).
Variables Top P : fc_object C.
Variable D : @finite_product_decomposition (fc_category C) Top P.
Variable products : forall A B : fc_object (@fc_slice C P),
  @finite_product_decomposition (fc_category (@fc_slice C P)) A B.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis hom_prime : forall X : fc_object C, coprime p #|fc_hom C X Top|.
Local Notation R := [the idomainType of (DPPrimeLocal.type p : Type)].

Lemma centric_top_mark_unit (X : fc_object (@fc_slice C P)) :
    burnside_mark X (burnside_top_element D R) \is a GRing.unit.
Proof.
rewrite burnside_top_mark.
exact (@DPPrimeLocalIntegers.natural_unit p hp #|fc_hom C (projT1 X) Top|
  (hom_prime (projT1 X))).
Qed.

Definition centric_top_inverse : burnside_module (@fc_slice C P) R :=
  @burnside_unit_marks_inverse (@fc_slice C P) R products
    (@fc_slice_terminal C P) (burnside_top_element D R).

Theorem centric_top_inverse_right :
    burnside_mul products (burnside_top_element D R) centric_top_inverse =
      burnside_one R (@fc_slice_terminal C P).
Proof.
apply: (@burnside_unit_marks_inverse_right (@fc_slice C P) R
  (@centric_slice_rank S F P)).
- move=> X Y f; exact: centric_slice_rank_le f.
- move=> X Y f h; exists (centric_slice_equal_rank_iso f h).
  exact: centric_slice_equal_rank_iso_hom.
- exact: burnside_prime_local_charzero.
- exact: centric_top_mark_unit.
Qed.

Theorem centric_top_inverse_left :
    burnside_mul products centric_top_inverse (burnside_top_element D R) =
      burnside_one R (@fc_slice_terminal C P).
Proof.
apply: (@burnside_unit_marks_inverse_left (@fc_slice C P) R
  (@centric_slice_rank S F P)).
- move=> X Y f; exact: centric_slice_rank_le f.
- move=> X Y f h; exists (centric_slice_equal_rank_iso f h).
  exact: centric_slice_equal_rank_iso_hom.
- exact: burnside_prime_local_charzero.
- exact: centric_top_mark_unit.
Qed.

End CentricTopUnit.

Print Assumptions centric_top_mark_unit.
Print Assumptions centric_top_inverse_right.
Print Assumptions centric_top_inverse_left.
