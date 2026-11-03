(** Actual F_p-valued Mackey coefficients on a Z_(p)-module killed by p,
    and transport through the genuine scalar-change higher-limit theorem. *)
From mathcomp Require Import all_boot all_algebra zmodp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  MackeyStructures MackeyBarReduction PrimeLocalRing PrimeLocalResidue
  ModuleScalarDescent BarScalarDescent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPScalarDescent DPBarScalarDescent DPPrimeLocal DPPrimeLocalResidue.
Local Open Scope ring_scope.

Module DPPrimeLocalTorsion.
Section Torsion.
Variable p : nat.
Hypothesis hp : prime p.
Local Notation Zp := [the comPzRingType of (DPPrimeLocal.type p : Type)].
Variable C : category.
Variable shape : mackey_shape C.
Variable M : mackey_module Zp shape.
Hypothesis killed : forall P (x : mackey_value M P), p%:R *: x = 0.

Lemma residue_kernel_annihilates P a : residue hp a = 0 ->
  forall x : mackey_value M P, a *: x = 0.
Proof.
move/(residue_kernel hp)=> [b <-] x.
by rewrite mulrC -scalerA killed scaler0.
Qed.

Definition torsion_field_mackey : mackey_module [the comPzRingType of 'F_p] shape :=
  @descended_mackey Zp [the comPzRingType of 'F_p] (residue hp)
    (residue_surjective hp) C shape M (@residue_kernel_annihilates).

Variable D : category.
Variable L : functor D C.

Theorem torsion_field_acyclic :
  mackey_bar_acyclic L torsion_field_mackey -> mackey_bar_acyclic L M.
Proof.
exact: (@descended_mackey_bar_acyclic Zp [the comPzRingType of 'F_p] (residue hp)
  (residue_surjective hp) C shape M (@residue_kernel_annihilates) D L).
Qed.

Theorem torsion_acyclic_of_prime_field
    (field_acyclic : forall N : mackey_module [the comPzRingType of 'F_p] shape,
      mackey_bar_acyclic L N) : mackey_bar_acyclic L M.
Proof. apply: torsion_field_acyclic; exact: field_acyclic. Qed.

End Torsion.
End DPPrimeLocalTorsion.
