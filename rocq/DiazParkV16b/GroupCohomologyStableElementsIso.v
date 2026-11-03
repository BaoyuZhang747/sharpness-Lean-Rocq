(** The actual restriction identifies ordinary cohomology with its stable
    elements when the subgroup index is invertible in the coefficient ring. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure MackeyModuleCarriers.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyPullback
  GroupCohomologyHomogeneousRestriction GroupCohomologyTransferNative
  GroupCohomologyTransferIndex GroupCohomologyStableElementsBase.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DPGroupCohomologyPullback
  DPGroupCohomologyHomogeneousRestriction DPGroupCohomologyTransferNative
  DPGroupCohomologyTransferIndex DPGroupCohomologyStableElementsBase.
Local Open Scope ring_scope.

Module DPGroupCohomologyStableElementsIso.
Section Comparison.
Variable R : comPzRingType.
Variable G : finGroupType.
Variables P Q : {group G}.
Variable hPQ : P \subset Q.
Variable A : lmodType R.
Variable n : nat.

Definition stable_subspace : module_subspace (value R [the finGroupType of [subg P]] A n).
Proof.
refine (@ModuleSubspace R _ (@stable R G P Q A n) _ _ _).
- move=> L hLP x hx hLx; by rewrite !module_hom_zero.
- move=> z w hz hw L hLP x hx hLx.
  by rewrite !module_hom_add hz // hw.
- move=> r z hz L hLP x hx hLx; by rewrite !module_hom_scale hz.
Defined.

Definition stable_module := [the lmodType R of submodule_carrier stable_subspace].

Definition stable_restriction : module_hom
    (value R [the finGroupType of [subg Q]] A n) stable_module.
Proof.
exists (fun z => @submodule_in R _ stable_subspace
  (module_hom_fun (pull A (subgroup_nested_hom hPQ) n) z)
  (@restriction_stable R G P Q hPQ A n z)).
move=> r z w; apply submodule_val_injective.
rewrite submodule_val_linear; exact: module_hom_linear.
Defined.

Variable u : R.
Hypothesis hu : u * (indexg Q P)%:R = 1.

Definition stable_inverse : module_hom stable_module
    (value R [the finGroupType of [subg Q]] A n).
Proof.
exists (fun z => u *: module_hom_fun (transfer A hPQ n) (submodule_val z)).
move=> r z w; rewrite submodule_val_linear module_hom_linear scalerDr !scalerA.
by rewrite (mulrC u r).
Defined.

Lemma stable_restriction_inverse z : stable_inverse (stable_restriction z) = z.
Proof.
change (u *: module_hom_fun (transfer A hPQ n)
  (module_hom_fun (pull A (subgroup_nested_hom hPQ) n) z) = z).
by rewrite transfer_restriction_index -scaler_nat scalerA hu scale1r.
Qed.

Lemma stable_inverse_restriction z : stable_restriction (stable_inverse z) = z.
Proof.
apply submodule_val_injective.
change (module_hom_fun (pull A (subgroup_nested_hom hPQ) n)
  (u *: module_hom_fun (transfer A hPQ n) (submodule_val z)) = submodule_val z).
rewrite module_hom_scale
  (@restriction_transfer_stable_index R G P Q hPQ A n _ (submodule_val_mem z)).
by rewrite -scaler_nat scalerA hu scale1r.
Qed.

Definition restriction_stable_iso : @isomorphism (module_category R)
    (value R [the finGroupType of [subg Q]] A n) stable_module.
Proof.
refine (@Build_isomorphism (module_category R) _ _ stable_restriction stable_inverse _ _).
- apply module_hom_ext; exact: stable_restriction_inverse.
- apply module_hom_ext; exact: stable_inverse_restriction.
Defined.

Theorem restriction_stable_iso_value z :
  submodule_val (module_hom_fun (iso_hom restriction_stable_iso) z) =
    module_hom_fun (pull A (subgroup_nested_hom hPQ) n) z.
Proof. reflexivity. Qed.

Theorem restriction_stable_iso_inverse z :
  module_hom_fun (iso_inv restriction_stable_iso) z =
    u *: module_hom_fun (transfer A hPQ n) (submodule_val z).
Proof. reflexivity. Qed.

End Comparison.
End DPGroupCohomologyStableElementsIso.
