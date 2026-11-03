(** Transport of actual subquotients along a module isomorphism that is
    proved to preserve both displayed subspaces. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps HomologicalModuleIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.

Module DPSubquotientModuleIso.
Section Iso.
Variable R : pzRingType.
Variables V W : lmodType R.
Variables Z B : module_subspace V.
Variables Z' B' : module_subspace W.
Variable e : @isomorphism (module_category R) V W.
Hypothesis hz : forall x, Z x <-> Z' (module_hom_fun (iso_hom e) x).
Hypothesis hb : forall x, B x <-> B' (module_hom_fun (iso_hom e) x).

Definition subquotient (U : lmodType R) (S T : module_subspace U) : lmodType R :=
  module_quotient (linear_preimage (submodule_inclusion S) T).

Definition subquotient_cycle_map : {linear submodule_carrier Z -> submodule_carrier Z'} :=
  @submodule_map R V W (module_hom_to_linear (iso_hom e)) Z Z' (fun x hx => proj1 (hz x) hx).

Definition subquotient_class_map (x : submodule_carrier Z) : subquotient Z' B' :=
  quotient_pi (linear_preimage (submodule_inclusion Z') B') (subquotient_cycle_map x).

Lemma subquotient_class_map_linear : linear subquotient_class_map.
Proof. intros a x y; by rewrite /subquotient_class_map !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build R (submodule_carrier Z) (subquotient Z' B') _
  subquotient_class_map subquotient_class_map_linear.

Lemma subquotient_class_map_kernel x :
    linear_preimage (submodule_inclusion Z) B x <-> subquotient_class_map x=0.
Proof.
rewrite /subquotient_class_map quotient_pi_kernel.
change (B (submodule_val x) <-> B' (module_hom_fun (iso_hom e) (submodule_val x))); exact: hb.
Qed.

Lemma subquotient_class_map_surjective (y : subquotient Z' B') : exists x, subquotient_class_map x=y.
Proof.
have [z <-] := quotient_pi_surjective y.
have hx : Z (module_hom_fun (iso_inv e) (submodule_val z)).
  apply (proj2 (hz _)); rewrite module_iso_inv_hom_apply; exact: submodule_val_mem.
exists (@submodule_in R V Z (module_hom_fun (iso_inv e) (submodule_val z)) hx).
unfold subquotient_class_map; f_equal; apply submodule_val_injective; exact: module_iso_inv_hom_apply.
Qed.

Definition subquotient_iso : @isomorphism (module_category R) (subquotient Z B) (subquotient Z' B') :=
  @quotient_linear_iso R (submodule_carrier Z) (subquotient Z' B')
    (linear_preimage (submodule_inclusion Z) B) subquotient_class_map
    subquotient_class_map_kernel subquotient_class_map_surjective.

Lemma subquotient_iso_pi (x : submodule_carrier Z) :
    module_hom_fun (iso_hom subquotient_iso) (quotient_pi (linear_preimage (submodule_inclusion Z) B) x)=
      subquotient_class_map x.
Proof.
change (@quotient_iso_map R (submodule_carrier Z) (subquotient Z' B')
  (linear_preimage (submodule_inclusion Z) B) subquotient_class_map subquotient_class_map_kernel
  (quotient_pi (linear_preimage (submodule_inclusion Z) B) x)=subquotient_class_map x).
exact: quotient_iso_map_pi.
Qed.

End Iso.
End DPSubquotientModuleIso.
