(** The actual short exact sequence from a coefficient diagram to its
    zero-extended restriction, with its genuine kernel subdiagram. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules ModuleDiagrams
  ModuleInfrastructure MackeyModuleCarriers HomologicalComplex
  BarComplex BarNaturality BarExactness CategoryAtomicDeletionCore
  CategoryAtomicDeletionAdjunction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkBarComplex DiazParkBarNaturality
  DiazParkBarExactness.
Local Open Scope ring_scope.

Section Deletion.
Variable R : pzRingType.
Variable C : category.
Variable P : C -> Prop.
Variable Pup : forall (x y : C), hom C x y -> P x -> P y.
Variable D : module_codiagram R C.

Definition deletion_truncation :=
  zero_extension Pup (fobj (full_restriction R P) D).
Definition deletion_kernel := diagram_kernel (zero_extension_unit Pup D).
Definition deletion_inclusion : nat_trans deletion_kernel D :=
  diagram_kernel_inclusion (zero_extension_unit Pup D).

Definition deletion_bar_short_exact : degreewise_short_exact
    (bar_cochain_map deletion_inclusion) (bar_cochain_map (zero_extension_unit Pup D)).
Proof.
apply: (@bar_short_exact R C deletion_kernel D deletion_truncation
  deletion_inclusion (zero_extension_unit Pup D)).
- move=> x; exact: diagram_kernel_inclusion_injective.
- move=> x v; exact (submodule_val_mem v).
- move=> x v hv.
  exists (@submodule_in R (fobj D x)
    (diagram_kernel_subspace (zero_extension_unit Pup D) x) v hv); reflexivity.
- exact: zero_extension_unit_surjective.
Defined.

Lemma deletion_kernel_inside x : P x -> forall v : fobj deletion_kernel x, v = 0.
Proof.
move=> hx v; apply submodule_val_injective.
apply (@zero_extension_unit_injective_inside R C P Pup D x hx).
rewrite module_hom_zero; exact (submodule_val_mem v).
Qed.

Lemma deletion_kernel_of_zero x :
  (forall v : fobj D x, v = 0) -> forall v : fobj deletion_kernel x, v = 0.
Proof. move=> hx v; apply submodule_val_injective; exact: hx. Qed.

Lemma deletion_truncation_of_zero x :
  (forall v : fobj D x, v = 0) -> forall v : fobj deletion_truncation x, v = 0.
Proof. move=> hx v; apply functional_extensionality_dep => h; exact: hx. Qed.

Lemma deletion_truncation_outside x :
  ~ P x -> forall v : fobj deletion_truncation x, v = 0.
Proof. exact: zero_extension_outside. Qed.

End Deletion.
