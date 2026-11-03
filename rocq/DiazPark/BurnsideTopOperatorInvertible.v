From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryFinite CategoryFiniteClasses
  CategoryFiniteProducts CategoryFinitePullbacks CategoryFiniteSlice
  CategoryFiniteSliceProducts FusionSystems FusionFiniteCategory
  BurnsideAlgebra BurnsideMarkAlgebra BurnsideTopElement BurnsideTopUnit
  BurnsideOperators BurnsideOperatorUnit MackeyPair PrimeLocalRing PrimeLocalMackey.
Import GRing.Theory DPPrimeLocal DPPrimeLocalMackey.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Inverse.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Local Notation C := (DPFusionFinite.centric_finite_category F).
Variables Top P : fc_object C.
Variable D : @finite_product_decomposition (fc_category C) Top P.
Variable pullbacks : forall (A B : fc_object C)
  (f : fc_hom C A P) (g : fc_hom C B P),
  @finite_pullback_decomposition (fc_category C) A B P f g.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis hom_prime : forall X : fc_object C, coprime p #|fc_hom C X Top|.
Variable R : comPzRingType.
Variable phi : {rmorphism DPPrimeLocal.type p -> R}.
Variable M : mackey_pair R (fc_category C).
Hypothesis pullback_mackey : forall (A B : fc_object C)
  (f : fc_hom C A P) (g : fc_hom C B P) (x : pair_value M A),
  pair_pull M g (pair_push M f x) =
    \sum_(i : pb_index (pullbacks f g))
      pair_push M (pb_right (pullbacks f g) i)
        (pair_pull M (pb_left (pullbacks f g) i) x).

Local Notation M0 := (restrict_mackey_pair phi M).
Local Notation Zp := [the idomainType of (DPPrimeLocal.type p : Type)].
Local Notation products := (burnside_slice_products pullbacks).

Definition top_transfer_restriction (x : pair_value M P) :=
  \sum_(i : fp_index D) pair_push M (fp_right D i) (pair_pull M (fp_right D i) x).

Definition top_transfer_inverse (x : pair_value M P) :=
  burnside_action (M := M0) (centric_top_inverse D products p) x.

Lemma top_transfer_inverse_right : cancel top_transfer_restriction top_transfer_inverse.
Proof.
move=> x.
change (burnside_action (M := M0) (centric_top_inverse D products p)
  (\sum_(i : fp_index D) pair_push M0 (fp_right D i) (pair_pull M0 (fp_right D i) x)) = x).
rewrite -burnside_action_top.
rewrite -(@burnside_action_mul C _ M0 P pullbacks pullback_mackey).
rewrite (centric_top_inverse_right D products hp hom_prime).
exact: burnside_action_one.
Qed.

Lemma top_transfer_inverse_left : cancel top_transfer_inverse top_transfer_restriction.
Proof.
move=> x.
change ((\sum_(i : fp_index D) pair_push M0 (fp_right D i)
  (pair_pull M0 (fp_right D i)
    (burnside_action (M := M0) (centric_top_inverse D products p) x))) = x).
rewrite -burnside_action_top.
rewrite -(@burnside_action_mul C _ M0 P pullbacks pullback_mackey).
rewrite (centric_top_inverse_left D products hp hom_prime).
exact: burnside_action_one.
Qed.

Theorem top_transfer_restriction_bijective : bijective top_transfer_restriction.
Proof.
exists top_transfer_inverse; [exact: top_transfer_inverse_right | exact: top_transfer_inverse_left].
Qed.
End Inverse.

Print Assumptions top_transfer_inverse_right.
Print Assumptions top_transfer_inverse_left.
Print Assumptions top_transfer_restriction_bijective.
