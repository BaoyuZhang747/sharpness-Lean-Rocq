From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import HomologicalComplex ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory DiazParkHomological.
Local Open Scope ring_scope.

(** Actual cycle/boundary quotient modules.  This construction concerns an
    arbitrary given cochain complex; it is not a definition of derived limits
    and does not replace the separate comparison with Ext.  The coefficient
    ring may be noncommutative or the zero ring. *)
Module DiazParkCohomology.

Section Cohomology.
Variable R : pzRingType.

Definition cycle_subspace (C : @cochain_complex R) n :=
  linear_kernel (cochain_d C n).

Definition boundary_subspace (C : @cochain_complex R) n :
    module_subspace (cochain_term C n) :=
  match n as k return module_subspace (cochain_term C k) with
  | 0%N => subspace_zero_space (cochain_term C 0%N)
  | k.+1 => linear_image (cochain_d C k)
  end.

Lemma boundary_subspaceE (C : @cochain_complex R) n
    (x : cochain_term C n) :
  boundary_subspace C n x <-> coboundary C n x.
Proof. by case: n x. Qed.

Lemma boundaries_are_cycles (C : @cochain_complex R) n :
  subspace_le (boundary_subspace C n) (cycle_subspace C n).
Proof.
move=> x /boundary_subspaceE hx.
exact: coboundary_cocycle hx.
Qed.

Definition cycle_module (C : @cochain_complex R) n :=
  submodule_carrier (cycle_subspace C n).

Definition cycle_inclusion (C : @cochain_complex R) n :
    {linear cycle_module C n -> cochain_term C n} :=
  (val : {linear cycle_module C n -> cochain_term C n}).

Definition boundaries_in_cycles (C : @cochain_complex R) n :=
  linear_preimage (cycle_inclusion C n) (boundary_subspace C n).

Definition cohomology (C : @cochain_complex R) n :=
  module_quotient (boundaries_in_cycles C n).

Definition cycle_of_cocycle (C : @cochain_complex R) n
    (x : cochain_term C n) (hx : cocycle C n x) : cycle_module C n :=
  @submodule_in R (cochain_term C n) (cycle_subspace C n) x hx.

Definition cohomology_class (C : @cochain_complex R) n
    (x : cochain_term C n) (hx : cocycle C n x) : cohomology C n :=
  quotient_pi (boundaries_in_cycles C n) (cycle_of_cocycle hx).

Lemma cohomology_class_zero (C : @cochain_complex R) n
    (x : cochain_term C n) (hx : cocycle C n x) :
  cohomology_class hx = 0 <-> coboundary C n x.
Proof.
rewrite /cohomology_class quotient_pi_kernel.
exact: boundary_subspaceE.
Qed.

(** This equivalence is proved using surjectivity of the actual quotient map.
    Consequently the vanishing predicate is about the constructed module,
    rather than a substitute definition of cohomology. *)
Theorem cohomology_zero_iff (C : @cochain_complex R) n :
  (forall q : cohomology C n, q = 0) <->
    (forall x : cochain_term C n, cocycle C n x -> coboundary C n x).
Proof.
split.
- move=> h x hx; apply/(cohomology_class_zero hx); exact: h.
- move=> h q.
  have [z <-] := quotient_pi_surjective q.
  apply/quotient_pi_kernel; apply/boundary_subspaceE.
  exact: h _ (submodule_val_mem z).
Qed.

Lemma positive_acyclic_cohomology (C : @cochain_complex R) :
  positive_acyclic C <->
    forall n (q : cohomology C n.+1), q = 0.
Proof.
split.
- move=> h n; apply/cohomology_zero_iff; exact: h n.
- move=> h n; apply/cohomology_zero_iff; exact: h n.
Qed.

Lemma all_degree_acyclic_cohomology (C : @cochain_complex R) :
  all_degree_acyclic C <-> forall n (q : cohomology C n), q = 0.
Proof.
split.
- move=> h n; apply/cohomology_zero_iff; exact: h n.
- move=> h n; apply/cohomology_zero_iff; exact: h n.
Qed.

End Cohomology.
End DiazParkCohomology.
