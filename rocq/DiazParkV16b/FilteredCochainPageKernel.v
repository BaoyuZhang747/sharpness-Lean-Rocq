(** The next-page denominator is precisely the kernel of the actual map
    from next cycles to homology of the preceding page. *)
From Coq Require Import ZArith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  MackeyModuleMaps HomologicalComplex.
From DiazParkV16b Require Import FilteredCochainCycles FilteredCochainPages
  FilteredCochainPageHomology FilteredCochainPageCycleLifting FilteredCochainPageRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPFilteredCycles DPFilteredPages
  DPFilteredPageHomology DPFilteredPageCycleLifting DPFilteredPageRepresentatives.
Local Open Scope ring_scope.

Module DPFilteredPageKernel.
Section Kernel.
Variable R : pzRingType.
Variable C : cochain_complex R.
Variable F : cochain_filtration C.

Lemma page_pi_class r p n (z : page_cycle_module F r p n) :
    quotient_pi (page_denominator F r p n) z = page_class (submodule_val_mem z).
Proof. unfold page_class; f_equal; apply submodule_val_injective; reflexivity. Qed.

Lemma next_cycle_boundary_iff r p n x (hx : almost_cycles F r.+2 p n x) :
    page_boundaries F r p n (page_class (next_cycle_old hx)) <-> page_relations F r.+1 p n x.
Proof.
split.
- destruct n.
  + intro hb; change (page_class (next_cycle_old hx)=0) in hb.
    have hr := proj1 (page_class_zero (next_cycle_old hx)) hb.
    apply: (@next_relation_of_old_difference R C F r p 0%N x 0 hx (subspace_zero _)).
    by rewrite subr0.
  + intros [w hw]; have [z hz] := quotient_pi_surjective w.
    change (page_incoming w=page_class (next_cycle_old hx)) in hw.
    rewrite -hz page_pi_class page_incoming_class in hw.
    have hy : filtered_boundaries F r.+1 p n.+1 (cochain_d C n (submodule_val z)).
      split; [exact (proj1 (incoming_d_cycles (submodule_val_mem z)))|].
      exists (submodule_val z); split; [exact (proj1 (submodule_val_mem z))|reflexivity].
    apply: (@next_relation_of_old_difference R C F r p n.+1 x _ hx hy).
    apply (proj1 (page_class_eq (next_cycle_old hx) (incoming_d_cycles (submodule_val_mem z)))); symmetry; exact hw.
- intros [a [b [ha [hb hab]]]].
  destruct n.
  + have hb0 : b=0 := proj2 hb.
    change (page_class (next_cycle_old hx)=0).
    apply (proj2 (page_class_zero (next_cycle_old hx))).
    have hxa : x=a by rewrite -hab hb0 addr0.
    rewrite hxa; apply page_relations_next; apply: almost_cycles_mono ha; lia.
  + destruct hb as [hb [v [hv hdv]]].
    have hvcycle : almost_cycles F r.+1 (Z.sub p (Z.of_nat r.+1)) n v.
      split; [exact hv|].
      change (filtration F (Z.add (Z.sub p (Z.of_nat r.+1)) (Z.of_nat r.+1)) n.+1 (cochain_d C n v)).
      by rewrite incoming_index hdv.
    exists (page_class hvcycle).
    change (page_incoming (page_class hvcycle)=page_class (next_cycle_old hx)).
    rewrite page_incoming_class.
    apply (proj2 (page_class_eq (incoming_d_cycles hvcycle) (next_cycle_old hx))).
    rewrite hdv.
    have he : b-x = -a by rewrite -hab opprD addrCA subrr addr0.
    rewrite he; apply subspace_opp; apply page_relations_next; apply: almost_cycles_mono ha; lia.
Qed.

Definition next_cycle_to_homology_cycle r p n (x : page_cycle_module F r.+1 p n) :
    page_homology_cycles F r p n :=
  @submodule_in R (page F r p n) (linear_kernel (page_d F r p n))
    (next_cycle_to_page x) (next_cycle_to_page_cycle x).

Lemma next_cycle_to_homology_cycle_linear r p n : linear (@next_cycle_to_homology_cycle r p n).
Proof. intros a x y; apply submodule_val_injective; exact: linearP. Qed.
HB.instance Definition _ r p n := GRing.isLinear.Build R (page_cycle_module F r.+1 p n)
  (page_homology_cycles F r p n) _ (@next_cycle_to_homology_cycle r p n)
  (@next_cycle_to_homology_cycle_linear r p n).

Definition next_cycle_to_homology r p n (x : page_cycle_module F r.+1 p n) : page_homology F r p n :=
  quotient_pi (page_homology_relations F r p n) (next_cycle_to_homology_cycle x).

Lemma next_cycle_to_homology_linear r p n : linear (@next_cycle_to_homology r p n).
Proof. intros a x y; by rewrite /next_cycle_to_homology !linearP. Qed.
HB.instance Definition _ r p n := GRing.isLinear.Build R (page_cycle_module F r.+1 p n)
  (page_homology F r p n) _ (@next_cycle_to_homology r p n) (@next_cycle_to_homology_linear r p n).

Lemma next_cycle_to_homology_kernel r p n x :
    page_denominator F r.+1 p n x <-> next_cycle_to_homology x=0.
Proof.
rewrite /next_cycle_to_homology quotient_pi_kernel.
change (page_relations F r.+1 p n (submodule_val x) <-> page_boundaries F r p n (next_cycle_to_page x)).
have he : next_cycle_to_page x = page_class (next_cycle_old (submodule_val_mem x)).
  unfold next_cycle_to_page, page_class; f_equal; apply submodule_val_injective; reflexivity.
rewrite he; symmetry; exact: next_cycle_boundary_iff.
Qed.

Lemma next_cycle_to_homology_surjective r p n (y : page_homology F r p n) :
    exists x, next_cycle_to_homology x=y.
Proof.
have [z <-] := quotient_pi_surjective y.
have [w hw] := quotient_pi_surjective (submodule_val z).
have hd : page_d F r p n (quotient_pi (page_denominator F r p n) w)=0.
  rewrite hw; exact (submodule_val_mem z).
have [x hx] := page_cycle_lift hd.
exists x; unfold next_cycle_to_homology; f_equal; apply submodule_val_injective.
change (next_cycle_to_page x=submodule_val z); by rewrite hx hw.
Qed.

End Kernel.
End DPFilteredPageKernel.
