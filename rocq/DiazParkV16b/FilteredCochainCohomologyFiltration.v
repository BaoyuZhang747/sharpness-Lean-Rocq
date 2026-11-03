(** Literal image filtration on the actual cohomology of the given complex.
    Its generators are filtered genuine cocycles, not approximate cycles. *)
From Coq Require Import ZArith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps.
From DiazParkV16b Require Import FilteredCochainCycles SubquotientModuleIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DPFilteredCycles DPSubquotientModuleIso.
Local Open Scope ring_scope.

Module DPFilteredCohomologyFiltration.
Section Filtration.
Variable R : pzRingType.
Variable C : cochain_complex R.
Variable F : cochain_filtration C.

Definition filtered_cocycles p n : module_subspace (cochain_term C n) :=
  subspace_inter (filtration F p n) (cycle_subspace C n).

Definition filtered_cocycle_to_cycle p n : {linear submodule_carrier (filtered_cocycles p n) -> cycle_module C n} :=
  @submodule_map R (cochain_term C n) (cochain_term C n) (idfun : {linear _ -> _})
    (filtered_cocycles p n) (cycle_subspace C n) (fun x hx => proj2 hx).

Definition filtered_cocycle_class p n (x : submodule_carrier (filtered_cocycles p n)) : cohomology C n :=
  quotient_pi (boundaries_in_cycles C n) (filtered_cocycle_to_cycle p n x).

Lemma filtered_cocycle_class_linear p n : linear (@filtered_cocycle_class p n).
Proof. intros a x y; by rewrite /filtered_cocycle_class !linearP. Qed.
HB.instance Definition _ p n := GRing.isLinear.Build R (submodule_carrier (filtered_cocycles p n))
  (cohomology C n) _ (@filtered_cocycle_class p n) (@filtered_cocycle_class_linear p n).

Definition cohomology_filtration p n : module_subspace (cohomology C n) := linear_image (@filtered_cocycle_class p n).

Lemma cohomology_filtration_decreasing p q n (hpq : Z.le p q) :
    subspace_le (cohomology_filtration q n) (cohomology_filtration p n).
Proof.
intros x [z <-].
have hz : filtered_cocycles p n (submodule_val z).
  split; [exact (@filtration_decreasing R C F p q n hpq _ (proj1 (submodule_val_mem z)))|exact (proj2 (submodule_val_mem z))].
exists (@submodule_in R (cochain_term C n) (filtered_cocycles p n) (submodule_val z) hz).
change (quotient_pi (boundaries_in_cycles C n) (filtered_cocycle_to_cycle p n
  (@submodule_in R (cochain_term C n) (filtered_cocycles p n) (submodule_val z) hz)) =
  quotient_pi (boundaries_in_cycles C n) (filtered_cocycle_to_cycle q n z)).
f_equal; apply submodule_val_injective; reflexivity.
Qed.

Definition associated_graded p n : lmodType R := subquotient (cohomology_filtration p n) (cohomology_filtration (Z.succ p) n).

Definition filtered_cocycle_image p n (x : submodule_carrier (filtered_cocycles p n)) :
    submodule_carrier (cohomology_filtration p n) :=
  @submodule_in R (cohomology C n) (cohomology_filtration p n) (filtered_cocycle_class x) (ex_intro _ x erefl).

Lemma filtered_cocycle_image_linear p n : linear (@filtered_cocycle_image p n).
Proof. intros a x y; apply submodule_val_injective; exact: linearP. Qed.
HB.instance Definition _ p n := GRing.isLinear.Build R (submodule_carrier (filtered_cocycles p n))
  (submodule_carrier (cohomology_filtration p n)) _ (@filtered_cocycle_image p n) (@filtered_cocycle_image_linear p n).

Definition filtered_cocycle_graded p n (x : submodule_carrier (filtered_cocycles p n)) : associated_graded p n :=
  quotient_pi (linear_preimage (submodule_inclusion (cohomology_filtration p n)) (cohomology_filtration (Z.succ p) n))
    (filtered_cocycle_image x).

Lemma filtered_cocycle_graded_linear p n : linear (@filtered_cocycle_graded p n).
Proof. intros a x y; by rewrite /filtered_cocycle_graded !linearP. Qed.
HB.instance Definition _ p n := GRing.isLinear.Build R (submodule_carrier (filtered_cocycles p n))
  (associated_graded p n) _ (@filtered_cocycle_graded p n) (@filtered_cocycle_graded_linear p n).

Lemma filtered_cocycle_graded_surjective p n (y : associated_graded p n) : exists x, filtered_cocycle_graded x=y.
Proof.
have [z <-] := quotient_pi_surjective y.
have [x hx] := submodule_val_mem z.
exists x; unfold filtered_cocycle_graded; f_equal; apply submodule_val_injective; exact hx.
Qed.

Lemma cohomology_class_eq n x y (hx : cocycle C n x) (hy : cocycle C n y) :
    cohomology_class hx=cohomology_class hy <-> coboundary C n (x-y).
Proof.
split; intro h.
- apply/boundary_subspaceE; apply/subspace_predP.
  move/eqP: h; rewrite /cohomology_class quotient_pi_eq; exact (fun h => h).
- apply/eqP; rewrite /cohomology_class quotient_pi_eq; apply/subspace_predP.
  apply/boundary_subspaceE; exact h.
Qed.

Lemma filtered_cocycle_class_eq p q n (x : submodule_carrier (filtered_cocycles p n))
    (y : submodule_carrier (filtered_cocycles q n)) :
    filtered_cocycle_class x=filtered_cocycle_class y <-> coboundary C n (submodule_val x-submodule_val y).
Proof.
change (cohomology_class (proj2 (submodule_val_mem x))=cohomology_class (proj2 (submodule_val_mem y)) <->
  coboundary C n (submodule_val x-submodule_val y)).
exact: cohomology_class_eq.
Qed.

Lemma filtered_cocycle_graded_kernel p n (x : submodule_carrier (filtered_cocycles p n)) :
    filtered_cocycle_graded x=0 <->
      exists a b, filtered_cocycles (Z.succ p) n a /\ filtration F p n b /\ coboundary C n b /\ a+b=submodule_val x.
Proof.
rewrite /filtered_cocycle_graded quotient_pi_kernel.
change (cohomology_filtration (Z.succ p) n (filtered_cocycle_class x) <->
  exists a b, filtered_cocycles (Z.succ p) n a /\ filtration F p n b /\ coboundary C n b /\ a+b=submodule_val x).
split.
- intros [y hy].
  exists (submodule_val y),(submodule_val x-submodule_val y); split; [exact: submodule_val_mem|].
  split.
  + apply subspace_sub; [exact (proj1 (submodule_val_mem x))|].
    apply: (@filtration_decreasing R C F p (Z.succ p) n _ _ (proj1 (submodule_val_mem y))); lia.
  + split.
    * apply (proj1 (filtered_cocycle_class_eq x y)); symmetry; exact hy.
    * by rewrite addrC subrK.
- intros [a [b [ha [hb [hdb hab]]]]].
  exists (@submodule_in R (cochain_term C n) (filtered_cocycles (Z.succ p) n) a ha).
  apply (proj2 (filtered_cocycle_class_eq _ x)).
  change (coboundary C n (a-submodule_val x)).
  have he : a-submodule_val x = -b by rewrite -hab opprD addrA subrr add0r.
  rewrite he; apply/boundary_subspaceE; apply subspace_opp; apply/boundary_subspaceE; exact hdb.
Qed.

End Filtration.
End DPFilteredCohomologyFiltration.
