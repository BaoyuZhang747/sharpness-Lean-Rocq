(** Finite convergence is derived from actual degree bounds on the filtration.
    The stable page is identified with the associated graded of actual H(C). *)
From Coq Require Import ZArith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps HomologicalComplex
  HomologicalCohomology HomologicalModuleIso.
From DiazParkV16b Require Import FilteredCochainCycles FilteredCochainPages FilteredCochainCohomologyFiltration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso
  DPFilteredCycles DPFilteredPages DPFilteredCohomologyFiltration.
Local Open Scope ring_scope.

Module DPFilteredFiniteConvergence.
Section Convergence.
Variable R : pzRingType.
Variable C : cochain_complex R.
Variable F : cochain_filtration C.
Hypothesis hfull : forall p n x, Z.le p 0 -> filtration F p n x.
Hypothesis hbounded : forall p n x, Z.lt (Z.of_nat n) p -> filtration F p n x -> x=0.

Lemma true_cycles_almost r p n : subspace_le (filtered_cocycles F p n) (almost_cycles F r p n).
Proof.
intros x [hx hdx]; split; [exact hx|].
change (filtration F (Z.add p (Z.of_nat r)) n.+1 (cochain_d C n x)).
change (cochain_d C n x=0) in hdx; rewrite hdx; exact: subspace_zero.
Qed.

Lemma bounded_almost_true r p n (h : Z.lt (Z.of_nat n.+1) (Z.add p (Z.of_nat r))) :
    subspace_le (almost_cycles F r p n) (filtered_cocycles F p n).
Proof.
intros x [hx hdx]; split; [exact hx|].
exact (@hbounded (Z.add p (Z.of_nat r)) n.+1 (cochain_d C n x) h hdx).
Qed.

Lemma exhaustive_filtered_boundaries r p n (h : Z.le (Z.sub p (Z.of_nat r)) 0) x :
    filtered_boundaries F r p n x <-> filtration F p n x /\ coboundary C n x.
Proof.
split.
- intros [hx hb]; split; [exact hx|].
  destruct n; [exact hb|].
  destruct hb as [v [hv hdv]]; exists v; exact hdv.
- intros [hx hb]; split; [exact hx|].
  destruct n; [exact hb|].
  destruct hb as [v hdv]; exists v; split; [exact (@hfull _ n v h)|exact hdv].
Qed.

Variables (r : nat) (p : Z) (n : nat).
Hypothesis hhigh : Z.lt (Z.of_nat n.+1) (Z.add p (Z.of_nat r.+1)).
Hypothesis hlow : Z.le (Z.sub p (Z.of_nat r)) 0.

Definition stable_cycle_map : {linear page_cycle_module F r p n -> submodule_carrier (filtered_cocycles F p n)} :=
  @submodule_map R (cochain_term C n) (cochain_term C n) (idfun : {linear _ -> _})
    (almost_cycles F r.+1 p n) (filtered_cocycles F p n) (@bounded_almost_true r.+1 p n hhigh).

Definition stable_page_class (x : page_cycle_module F r p n) : associated_graded F p n :=
  filtered_cocycle_graded (stable_cycle_map x).

Lemma stable_page_class_linear : linear stable_page_class.
Proof. intros a x y; by rewrite /stable_page_class !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build R (page_cycle_module F r p n) (associated_graded F p n) _
  stable_page_class stable_page_class_linear.

Lemma stable_page_class_kernel x : page_denominator F r p n x <-> stable_page_class x=0.
Proof.
rewrite /stable_page_class filtered_cocycle_graded_kernel.
change (page_relations F r p n (submodule_val x) <->
  exists a b, filtered_cocycles F (Z.succ p) n a /\ filtration F p n b /\ coboundary C n b /\ a+b=submodule_val x).
split.
- intros [a [b [ha [hb hab]]]]; exists a,b; split.
  + apply: (@bounded_almost_true r (Z.succ p) n _ a ha); lia.
  + have hb' := proj1 (@exhaustive_filtered_boundaries r p n hlow b) hb.
    split; [exact (proj1 hb')|split; [exact (proj2 hb')|exact hab]].
- intros [a [b [ha [hb [hdb hab]]]]]; exists a,b; split.
  + exact: true_cycles_almost ha.
  + split; [apply (proj2 (@exhaustive_filtered_boundaries r p n hlow b)); split; assumption|exact hab].
Qed.

Lemma stable_page_class_surjective (y : associated_graded F p n) : exists x, stable_page_class x=y.
Proof.
have [z hz] := filtered_cocycle_graded_surjective y.
have hx : almost_cycles F r.+1 p n (submodule_val z) := @true_cycles_almost r.+1 p n _ (submodule_val_mem z).
exists (@submodule_in R (cochain_term C n) (almost_cycles F r.+1 p n) (submodule_val z) hx).
rewrite -hz; unfold stable_page_class; f_equal; apply submodule_val_injective; reflexivity.
Qed.

Definition stable_page_associated_graded_iso : @isomorphism (module_category R) (page F r p n) (associated_graded F p n) :=
  @quotient_linear_iso R (page_cycle_module F r p n) (associated_graded F p n)
    (page_denominator F r p n) stable_page_class stable_page_class_kernel stable_page_class_surjective.

Lemma stable_page_associated_graded_iso_pi x :
    module_hom_fun (iso_hom stable_page_associated_graded_iso) (quotient_pi (page_denominator F r p n) x)=stable_page_class x.
Proof.
change (@quotient_iso_map R (page_cycle_module F r p n) (associated_graded F p n)
  (page_denominator F r p n) stable_page_class stable_page_class_kernel
  (quotient_pi (page_denominator F r p n) x)=stable_page_class x).
exact: quotient_iso_map_pi.
Qed.

End Convergence.
End DPFilteredFiniteConvergence.
