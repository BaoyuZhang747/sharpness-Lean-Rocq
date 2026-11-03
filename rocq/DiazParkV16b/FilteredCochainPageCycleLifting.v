(** Actual lifting of cycles of d_r to the next filtered-cycle module. *)
From Coq Require Import ZArith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  MackeyModuleMaps HomologicalComplex.
From DiazParkV16b Require Import FilteredCochainCycles FilteredCochainPages FilteredCochainPageHomology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPFilteredCycles DPFilteredPages DPFilteredPageHomology.
Local Open Scope ring_scope.

Module DPFilteredPageCycleLifting.
Section Lifting.
Variable R : pzRingType.
Variable C : cochain_complex R.
Variable F : cochain_filtration C.

Lemma page_d_class r p n x (hx : almost_cycles F r.+1 p n x) :
    page_d F r p n (page_class hx) = page_class (almost_cycles_d hx).
Proof.
rewrite /page_class page_d_pi; f_equal; apply submodule_val_injective; reflexivity.
Qed.

Lemma next_cycle_old r p n : subspace_le (almost_cycles F r.+2 p n) (almost_cycles F r.+1 p n).
Proof. apply almost_cycles_mono; lia. Qed.

Lemma next_cycle_d_relation r p n x (hx : almost_cycles F r.+2 p n x) :
    page_relations F r (Z.add p (Z.of_nat r.+1)) n.+1 (cochain_d C n x).
Proof.
apply page_relations_next; split.
- have hdx := proj2 hx.
  change (filtration F (Z.succ (Z.add p (Z.of_nat r.+1))) n.+1 (cochain_d C n x)).
  have he : Z.succ (Z.add p (Z.of_nat r.+1)) = Z.add p (Z.of_nat r.+2) by lia.
  by rewrite he.
- change (filtration F (Z.add (Z.succ (Z.add p (Z.of_nat r.+1))) (Z.of_nat r)) n.+2
    (cochain_d C n.+1 (cochain_d C n x))).
  rewrite cochain_d2; exact: subspace_zero.
Qed.

Definition next_cycle_to_old_cycle r p n : {linear page_cycle_module F r.+1 p n -> page_cycle_module F r p n} :=
  @submodule_map R (cochain_term C n) (cochain_term C n) (idfun : {linear _ -> _})
    (almost_cycles F r.+2 p n) (almost_cycles F r.+1 p n) (@next_cycle_old r p n).

Definition next_cycle_to_page r p n (x : page_cycle_module F r.+1 p n) : page F r p n :=
  quotient_pi (page_denominator F r p n) (next_cycle_to_old_cycle r p n x).

Lemma next_cycle_to_page_linear r p n : linear (@next_cycle_to_page r p n).
Proof. intros a x y; by rewrite /next_cycle_to_page !linearP. Qed.
HB.instance Definition _ r p n := GRing.isLinear.Build R (page_cycle_module F r.+1 p n) (page F r p n) _
  (@next_cycle_to_page r p n) (@next_cycle_to_page_linear r p n).

Lemma next_cycle_to_page_cycle r p n x : page_d F r p n (next_cycle_to_page x) = 0.
Proof.
rewrite /next_cycle_to_page page_d_pi.
apply/(quotient_pi_kernel (page_denominator F r (Z.add p (Z.of_nat r.+1)) n.+1)).
exact: next_cycle_d_relation (submodule_val_mem x).
Qed.

Lemma page_cycle_lift r p n (x : page_cycle_module F r p n)
    (hx : page_d F r p n (quotient_pi (page_denominator F r p n) x) = 0) :
    exists y : page_cycle_module F r.+1 p n,
      next_cycle_to_page y = quotient_pi (page_denominator F r p n) x.
Proof.
rewrite page_d_pi in hx.
have hr := proj1 (quotient_pi_kernel (page_denominator F r (Z.add p (Z.of_nat r.+1)) n.+1)
  (page_cycle_d F r p n x)) hx.
destruct hr as [a [b [[ha hda] [[hb [v [hv hdv]]] hab]]]].
have hv' : filtration F (Z.succ p) n v.
  have he : Z.sub (Z.add p (Z.of_nat r.+1)) (Z.of_nat r) = Z.succ p by lia.
  change (filtration F (Z.sub (Z.add p (Z.of_nat r.+1)) (Z.of_nat r)) n v) in hv.
  by rewrite he in hv.
have hy : almost_cycles F r.+2 p n (submodule_val x-v).
  split.
  + apply subspace_sub; [exact: (proj1 (submodule_val_mem x))|].
    apply: (@filtration_decreasing R C F p (Z.succ p) n _ _ hv'); lia.
  + change (filtration F (Z.add p (Z.of_nat r.+2)) n.+1 (cochain_d C n (submodule_val x-v))).
    rewrite linearB hdv.
    change (a+b=cochain_d C n (submodule_val x)) in hab.
    rewrite -hab addrK.
    have he : Z.add p (Z.of_nat r.+2) = Z.succ (Z.add p (Z.of_nat r.+1)) by lia.
    by rewrite he.
exists (@submodule_in R (cochain_term C n) (almost_cycles F r.+2 p n) (submodule_val x-v) hy).
apply/eqP; rewrite quotient_pi_eq; apply/subspace_predP.
change (page_relations F r p n (submodule_val x-v-submodule_val x)).
have he : submodule_val x-v-submodule_val x = -v by rewrite addrAC subrr add0r.
rewrite he; apply subspace_opp; apply page_relations_next; split; [exact hv'|].
change (filtration F (Z.add (Z.succ p) (Z.of_nat r)) n.+1 (cochain_d C n v)).
rewrite hdv.
have he' : Z.add (Z.succ p) (Z.of_nat r) = Z.add p (Z.of_nat r.+1) by lia.
by rewrite he'.
Qed.

End Lifting.
End DPFilteredPageCycleLifting.
