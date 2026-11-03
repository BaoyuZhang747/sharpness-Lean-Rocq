(** Genuine spectral-page subquotients. The parameter r labels E_{r+1}, so
    every denominator is defined without truncated subtraction in page order.
    Filtration indices are integers, and degree-zero boundaries are zero. *)
From Coq Require Import ZArith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  MackeyModuleMaps HomologicalComplex.
From DiazParkV16b Require Import FilteredCochainCycles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPFilteredCycles.
Local Open Scope ring_scope.

Module DPFilteredPages.
Section Pages.
Variable R : pzRingType.
Variable C : cochain_complex R.
Variable F : cochain_filtration C.

Definition page_relations_condition r p n (x : cochain_term C n) : Prop :=
  exists a b, almost_cycles F r (Z.succ p) n a /\ filtered_boundaries F r p n b /\ a+b=x.
Arguments page_relations_condition r p n x : clear implicits.

Definition page_relations (r : nat) (p : Z) (n : nat) : module_subspace (cochain_term C n).
Proof.
refine (@ModuleSubspace R (cochain_term C n) (page_relations_condition r p n) _ _ _).
- exists 0,0; split; [exact: subspace_zero|]; split; [exact: subspace_zero|exact: addr0].
- intros x y [a [b [ha [hb hab]]]] [c [d [hc [hd hcd]]]].
  exists (a+c),(b+d); split; [exact: subspace_add ha hc|].
  split; [exact: subspace_add hb hd|].
  by rewrite addrACA hab hcd.
- intros t x [a [b [ha [hb hab]]]].
  exists (t*:a),(t*:b); split; [exact (@subspace_scale R _ (almost_cycles F r (Z.succ p) n) t a ha)|].
  split; [exact (@subspace_scale R _ (filtered_boundaries F r p n) t b hb)|].
  by rewrite -scalerDr hab.
Defined.

Lemma page_relations_cycles r p n : subspace_le (page_relations r p n) (almost_cycles F r.+1 p n).
Proof.
intros x [a [b [ha [hb <-]]]].
apply subspace_add.
- exact: next_column_almost_cycles ha.
- exact: filtered_boundaries_are_almost_cycles hb.
Qed.

Definition page_cycle_module r p n : lmodType R := submodule_carrier (almost_cycles F r.+1 p n).
Definition page_denominator r p n : module_subspace (page_cycle_module r p n) :=
  linear_preimage (submodule_inclusion (almost_cycles F r.+1 p n)) (page_relations r p n).
Definition page r p n : lmodType R := module_quotient (page_denominator r p n).

Definition page_class r p n (x : cochain_term C n) (hx : almost_cycles F r.+1 p n x) : page r p n :=
  quotient_pi (page_denominator r p n) (@submodule_in R (cochain_term C n) (almost_cycles F r.+1 p n) x hx).

Lemma page_class_zero r p n x (hx : almost_cycles F r.+1 p n x) :
    page_class hx = 0 <-> page_relations r p n x.
Proof. exact: quotient_pi_kernel. Qed.

Lemma page_relations_next r p n x : almost_cycles F r (Z.succ p) n x -> page_relations r p n x.
Proof. intro hx; exists x,0; split; [exact hx|]; split; [exact: subspace_zero|exact: addr0]. Qed.

Lemma page_relations_boundary r p n x : filtered_boundaries F r p n x -> page_relations r p n x.
Proof. intro hx; exists 0,x; split; [exact: subspace_zero|]; split; [exact hx|exact: add0r]. Qed.

Lemma page_relations_d r p n x : page_relations r p n x ->
    page_relations r (Z.add p (Z.of_nat r.+1)) n.+1 (cochain_d C n x).
Proof.
intros [a [b [[ha hda] [[hb hdb] <-]]]].
rewrite linearD (filtered_boundary_d_zero hdb) addr0.
apply page_relations_boundary; split.
- change (filtration F (Z.add p (Z.of_nat r.+1)) n.+1 (cochain_d C n a)).
  have he : Z.add p (Z.of_nat r.+1) = Z.add (Z.succ p) (Z.of_nat r) by lia.
  by rewrite he.
- exists a; split; [|reflexivity].
  change (filtration F (Z.sub (Z.add p (Z.of_nat r.+1)) (Z.of_nat r)) n a).
  have he : Z.sub (Z.add p (Z.of_nat r.+1)) (Z.of_nat r) = Z.succ p by lia.
  by rewrite he.
Qed.

Definition page_cycle_d r p n :
    {linear page_cycle_module r p n -> page_cycle_module r (Z.add p (Z.of_nat r.+1)) n.+1} :=
  @submodule_map R (cochain_term C n) (cochain_term C n.+1) (cochain_d C n)
    (almost_cycles F r.+1 p n) (almost_cycles F r.+1 (Z.add p (Z.of_nat r.+1)) n.+1)
    (fun x hx => almost_cycles_d hx).

Lemma page_cycle_d_relations r p n x : page_denominator r p n x ->
    page_denominator r (Z.add p (Z.of_nat r.+1)) n.+1 (page_cycle_d r p n x).
Proof. exact: page_relations_d. Qed.

Definition page_d r p n : {linear page r p n -> page r (Z.add p (Z.of_nat r.+1)) n.+1} :=
  @quotient_map R (page_cycle_module r p n) (page_cycle_module r (Z.add p (Z.of_nat r.+1)) n.+1)
    (page_cycle_d r p n) (page_denominator r p n)
    (page_denominator r (Z.add p (Z.of_nat r.+1)) n.+1) (@page_cycle_d_relations r p n).

Lemma page_d_pi r p n x : page_d r p n (quotient_pi (page_denominator r p n) x) =
    quotient_pi (page_denominator r (Z.add p (Z.of_nat r.+1)) n.+1) (page_cycle_d r p n x).
Proof. exact: quotient_map_pi. Qed.

Theorem page_d_squared r p n (x : page r p n) :
    page_d r (Z.add p (Z.of_nat r.+1)) n.+1 (page_d r p n x) = 0.
Proof.
have [z <-] := quotient_pi_surjective x.
rewrite !page_d_pi.
have hz : page_cycle_d r (Z.add p (Z.of_nat r.+1)) n.+1 (page_cycle_d r p n z) = 0.
  apply submodule_val_injective; exact: cochain_d2.
by rewrite hz linear0.
Qed.

End Pages.
End DPFilteredPages.
