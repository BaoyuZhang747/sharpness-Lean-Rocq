(** Actual constant-coefficient category-bar cohomology, its literal
    pullbacks, and the isomorphism constructed from an actual adjunction. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryAdjunction
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import CategoryBarPullbackConstant CategoryBarPullbackHomotopy.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DPCategoryBarConstant DPCategoryBarHomotopy.

Module DPCategoryConstantCohomology.
Section Cohomology.
Variable R : pzRingType.
Variable A : lmodType R.

Definition value (C : category) (n : nat) : lmodType R :=
  [the lmodType R of cohomology (constant_bar R C A) n].

Definition pull (C D : category) (F : functor C D) n :
    module_hom (value D n) (value C n) :=
  module_hom_of_linear (cohomology_map (constant_bar_pullback A F) n).

Lemma pull_identity (C : category) n :
    pull (functor_id C) n = module_hom_id (value C n).
Proof.
apply module_hom_ext=> q; have [z <-] := quotient_pi_surjective q.
change (cohomology_map (constant_bar_pullback A (functor_id C)) n (quotient_pi _ z) =
  quotient_pi _ z).
rewrite cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; exact: constant_bar_pullback_identity.
Qed.

Lemma pull_composition (C D E : category) (F : functor C D) (G : functor D E) n :
    pull (functor_comp F G) n = module_hom_comp (pull G n) (pull F n).
Proof.
apply module_hom_ext=> q; have [z <-] := quotient_pi_surjective q.
change (cohomology_map (constant_bar_pullback A (functor_comp F G)) n (quotient_pi _ z) =
  cohomology_map (constant_bar_pullback A F) n
    (cohomology_map (constant_bar_pullback A G) n (quotient_pi _ z))).
rewrite !cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; exact: constant_bar_pullback_composition.
Qed.

Theorem pull_nat_trans (C D : category) (F G : functor C D)
    (alpha : nat_trans F G) n : pull G n = pull F n.
Proof.
apply module_hom_ext=> q.
exact: cohomology_map_homotopy (constant_bar_nat_trans_homotopy A alpha) n q.
Qed.

Section Adjunction.
Variables C D : category.
Variables F : functor C D.
Variables G : functor D C.
Variable a : adjunction F G.

Lemma adjunction_hom_inv n : module_hom_comp (pull G n) (pull F n) = module_hom_id (value C n).
Proof.
rewrite -pull_composition (pull_nat_trans (adj_unit a)) pull_identity; reflexivity.
Qed.

Lemma adjunction_inv_hom n : module_hom_comp (pull F n) (pull G n) = module_hom_id (value D n).
Proof.
rewrite -pull_composition -(pull_nat_trans (adj_counit a)) pull_identity; reflexivity.
Qed.

Definition adjunction_iso n : @isomorphism (module_category R) (value C n) (value D n) :=
  @Build_isomorphism (module_category R) (value C n) (value D n)
    (pull G n) (pull F n) (adjunction_hom_inv n) (adjunction_inv_hom n).

Lemma adjunction_iso_hom n : iso_hom (adjunction_iso n) = pull G n.
Proof. reflexivity. Qed.

Lemma adjunction_iso_inv n : iso_inv (adjunction_iso n) = pull F n.
Proof. reflexivity. Qed.
End Adjunction.
End Cohomology.
Arguments value R A C n : clear implicits.
Arguments pull {R} A {C D} F n.
Arguments adjunction_iso {R} A {C D F G} a n.
End DPCategoryConstantCohomology.

Check DPCategoryConstantCohomology.adjunction_iso.
Check DPCategoryConstantCohomology.pull_nat_trans.
Print Assumptions DPCategoryConstantCohomology.adjunction_iso.
Print Assumptions DPCategoryConstantCohomology.pull_nat_trans.
