(** A native left shift of a nonnegative cochain complex. The cohomology
    comparison explicitly requires the omitted terms to vanish, which handles
    the new degree zero without discarding incoming boundaries silently. *)
From Coq Require Import Arith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalModuleIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.

Module DPCochainDegreeShift.
Section Shift.
Variable R : pzRingType.
Variable K : cochain_complex R.
Variable p : nat.

Definition degree_shift : cochain_complex R :=
  @CochainComplex R (fun n => cochain_term K (n+p)%coq_nat)
    (fun n => cochain_d K (n+p)%coq_nat)
    (fun n x => @cochain_d2 R K (n+p)%coq_nat x).

Hypothesis below_zero : forall n, (n < p)%coq_nat -> forall x : cochain_term K n, x = 0.

Lemma degree_shift_boundary n (x : cochain_term degree_shift n) :
    coboundary degree_shift n x <-> coboundary K (n+p)%coq_nat x.
Proof.
destruct n as [|n].
- change (x = 0 <-> coboundary K p x).
  split.
  + intro hx; subst x.
    change (coboundary K p (0 : cochain_term K p)).
    destruct p as [|k]; [reflexivity|].
    exists 0; exact: linear0.
  + move: x; change (forall x : cochain_term K p, coboundary K p x -> x = 0).
    destruct p as [|k]; [exact (fun x h => h)|].
    intros x [y hy].
    have yz : y = 0 := @below_zero k (Nat.lt_succ_diag_r k) y.
    by rewrite yz linear0 in hy; symmetry.
- reflexivity.
Qed.

Lemma degree_shift_quotient_kernel n (z : cycle_module degree_shift n) :
    boundaries_in_cycles degree_shift n z <->
      quotient_pi (boundaries_in_cycles K (n+p)%coq_nat) z = 0.
Proof.
rewrite quotient_pi_kernel.
change (boundary_subspace degree_shift n (submodule_val z) <->
  boundary_subspace K (n+p)%coq_nat (submodule_val z)).
rewrite !boundary_subspaceE; exact: degree_shift_boundary.
Qed.

Definition degree_shift_cohomology_iso n : @isomorphism (module_category R)
    (cohomology degree_shift n) (cohomology K (n+p)%coq_nat) :=
  @quotient_linear_iso R (cycle_module degree_shift n) (cohomology K (n+p)%coq_nat)
    (boundaries_in_cycles degree_shift n)
    (quotient_pi (boundaries_in_cycles K (n+p)%coq_nat))
    (@degree_shift_quotient_kernel n) (fun x => quotient_pi_surjective x).

Theorem degree_shift_cohomology_iso_class n (z : cycle_module degree_shift n) :
    module_hom_fun (iso_hom (degree_shift_cohomology_iso n))
      (quotient_pi (boundaries_in_cycles degree_shift n) z) =
        quotient_pi (boundaries_in_cycles K (n+p)%coq_nat) z.
Proof. exact: quotient_iso_map_pi. Qed.

End Shift.
End DPCochainDegreeShift.
