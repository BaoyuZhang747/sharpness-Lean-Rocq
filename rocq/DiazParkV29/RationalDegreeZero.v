(** Actual native group H^0, with its restriction and transfer coordinates. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp rat.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps HomologicalDegreeZero
  MackeyModuleCarriers MackeyModuleQuotient BarComplex BarDegreeZero.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyPullback
  GroupCohomologyTransferNative GroupCohomologyTransferIndex
  GroupCohomologyHomogeneousRestriction CochainZeroCycleNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology
  DiazParkHomologicalDegreeZero DiazParkBarComplex DiazParkBarDegreeZero
  DPGroupCohomology DPGroupCohomologyPullback DPGroupCohomologyTransferNative
  DPGroupCohomologyTransferIndex DPCochainZeroCycleNaturality.
Import DPGroupCohomologyHomogeneousRestriction.
Local Open Scope ring_scope.

Module DPV29RationalDegreeZero.
Section Zero.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable G : finGroupType.

Definition coordinate (q : value R G A 0) : A :=
  submodule_val (cohomology_zero_cycle (complex R G A) q) tt tt.

Definition constant_cycle (a : A) : cycle_module (complex R G A) 0.
Proof.
refine (@cycle_of_cocycle R (complex R G A) 0 (fun _ _ => a) _).
apply/bar_zero_cocycle_compatible; move=> x y f; reflexivity.
Defined.

Definition constant_class (a : A) : value R G A 0 :=
  quotient_pi (boundaries_in_cycles (complex R G A) 0) (constant_cycle a).

Lemma coordinate_constant a : coordinate (constant_class a) = a.
Proof. by rewrite /coordinate /constant_class cohomology_zero_cycle_pi. Qed.

Lemma constant_coordinate q : constant_class (coordinate q) = q.
Proof.
rewrite /constant_class -[RHS]cohomology_zero_pi_cycle.
congr (quotient_pi _ _); apply submodule_val_injective.
apply functional_extensionality_dep => x; case: x.
apply functional_extensionality_dep => t; by case: t.
Qed.

Definition coordinate_hom : module_hom (value R G A 0) A.
Proof.
exists coordinate; move=> r a b.
rewrite /coordinate linearP.
reflexivity.
Defined.

Definition constant_hom : module_hom A (value R G A 0).
Proof.
exists constant_class; move=> r a b.
rewrite /constant_class -linearP.
congr (quotient_pi _ _); apply submodule_val_injective; reflexivity.
Defined.

Definition degree_zero_iso : @isomorphism (module_category R) (value R G A 0) A.
Proof.
refine (@Build_isomorphism (module_category R) _ _ coordinate_hom constant_hom _ _).
- apply module_hom_ext => x; exact: constant_coordinate.
- apply module_hom_ext => x; exact: coordinate_constant.
Defined.

End Zero.

Lemma coordinate_pull (R : comPzRingType) (A : lmodType R)
    (G H : finGroupType) (f : {morphism [set: G] >-> H}) (q : value R H A 0) :
    coordinate (module_hom_fun (pull A f 0) q) = coordinate q.
Proof.
rewrite /coordinate.
change (submodule_val (cohomology_zero_cycle (complex R G A)
  (DiazParkCohomologyMaps.cohomology_map (pull_cochain A f) 0 q)) tt tt =
  submodule_val (cohomology_zero_cycle (complex R H A) q) tt tt).
rewrite cohomology_zero_cycle_map_val; reflexivity.
Qed.

Lemma coordinate_transfer (R : comPzRingType) (A : lmodType R)
    (G : finGroupType) (P Q : {group G}) (h : P \subset Q)
    (q : value R [the finGroupType of [subg P]] A 0) :
    coordinate (module_hom_fun (transfer A h 0) q) = coordinate q *+ indexg Q P.
Proof.
pose y := @constant_class R A [the finGroupType of [subg Q]] (coordinate q).
have hy : module_hom_fun (pull A (subgroup_nested_hom h) 0) y = q.
  apply (can_inj (@constant_coordinate R A [the finGroupType of [subg P]])).
  change (coordinate (module_hom_fun (pull A (subgroup_nested_hom h) 0) y) = coordinate q).
  by rewrite coordinate_pull coordinate_constant.
rewrite -hy transfer_restriction_index.
change (module_hom_fun (@coordinate_hom R A [the finGroupType of [subg Q]])
  (y *+ indexg Q P) = coordinate (module_hom_fun (pull A (subgroup_nested_hom h) 0) y) *+ indexg Q P).
rewrite coordinate_pull.
elim: (indexg Q P) => [|n IH]; first exact: module_hom_zero.
by rewrite !mulrS module_hom_add IH.
Qed.

End DPV29RationalDegreeZero.
