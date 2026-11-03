(** Native pullbacks on actual ordinary group-bar cohomology. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps BarPaths BarComplex
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyCoefficients CategoryBarPullbackPaths CategoryBarPullbackConstant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomology DPGroupCohomologyFunctor DPGroupCohomologyCoefficients
  DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkBarPaths DiazParkBarComplex DPCategoryBarPullback DPCategoryBarConstant.

Module DPGroupCohomologyPullback.
Section Pullbacks.
Variable R : comPzRingType.
Variable A : lmodType R.

Definition pull_cochain (G H : finGroupType)
    (f : {morphism [set: G] >-> H}) :
    cochain_map (complex R H A) (complex R G A) :=
  constant_bar_pullback A (group_functor f).

Lemma pull_cochain_at (G H : finGroupType)
    (f : {morphism [set: G] >-> H}) n
    (a : cochain_term (complex R H A) n) x (p : @path_from (group_category G) n x) :
  cochain_map_at (pull_cochain f) n a x p =
    a x (path_map_from (group_functor f) n x p).
Proof. reflexivity. Qed.

Definition pull (G H : finGroupType) (f : {morphism [set: G] >-> H}) n :
    module_hom (value R H A n) (value R G A n) :=
  module_hom_of_linear (cohomology_map (pull_cochain f) n).

Lemma pull_identity (G : finGroupType) n :
  pull (group_hom_identity G) n = module_hom_id (value R G A n).
Proof.
apply module_hom_ext => q.
have [z <-] := quotient_pi_surjective q.
change (cohomology_map (pull_cochain (group_hom_identity G)) n (quotient_pi _ z) =
  quotient_pi _ z).
rewrite cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective.
change (cochain_map_at (constant_bar_pullback A (group_functor (group_hom_identity G)))
  n (submodule_val z) = submodule_val z).
rewrite group_functor_identity; exact: constant_bar_pullback_identity.
Qed.

Lemma pull_composition (G H K : finGroupType)
    (f : {morphism [set: G] >-> H}) (g : {morphism [set: H] >-> K}) n :
  pull (group_hom_comp f g) n = module_hom_comp (pull g n) (pull f n).
Proof.
apply module_hom_ext => q.
have [z <-] := quotient_pi_surjective q.
change (cohomology_map (pull_cochain (group_hom_comp f g)) n (quotient_pi _ z) =
  cohomology_map (pull_cochain f) n
    (cohomology_map (pull_cochain g) n (quotient_pi _ z))).
rewrite !cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective.
change (cochain_map_at (constant_bar_pullback A (group_functor (group_hom_comp f g)))
    n (submodule_val z) =
  cochain_map_at (constant_bar_pullback A (group_functor f)) n
    (cochain_map_at (constant_bar_pullback A (group_functor g)) n (submodule_val z))).
rewrite group_functor_composition; exact: constant_bar_pullback_composition.
Qed.

End Pullbacks.

Arguments pull_cochain {R} A {G H} f.
Arguments pull {R} A {G H} f n.

Lemma pull_coefficient_naturality (R : comPzRingType) (A B : lmodType R)
    (G H : finGroupType) (f : {morphism [set: G] >-> H}) (u : module_hom A B) n :
  module_hom_comp (pull A f n) (coefficient_map G u n) =
    module_hom_comp (coefficient_map H u n) (pull B f n).
Proof.
apply module_hom_ext => q.
have [z <-] := quotient_pi_surjective q.
change (cohomology_map (coefficient_cochain_map G u) n
    (cohomology_map (pull_cochain A f) n (quotient_pi _ z)) =
  cohomology_map (pull_cochain B f) n
    (cohomology_map (coefficient_cochain_map H u) n (quotient_pi _ z))).
rewrite !cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; reflexivity.
Qed.

End DPGroupCohomologyPullback.
