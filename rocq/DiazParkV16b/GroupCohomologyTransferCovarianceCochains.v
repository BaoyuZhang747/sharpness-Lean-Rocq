(** The actual shared-resolution transfer square for subgroup-image maps. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryDiagramHom
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  BarFreeModule MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import GroupCohomologyHomogeneousPaths
  GroupCohomologyHomogeneousMaps GroupCohomologyHomogeneousComplex
  GroupCohomologyHomogeneousEquivariance GroupCohomologyHomogeneousCohomology
  GroupCohomologyTransferCosets GroupCohomologyTransferHomogeneous
  GroupCohomologyHomogeneousSemilinear GroupCohomologyCosetSumsCovariance
  GroupCohomologyCosetSumsTowerCoordinates GroupCohomologyTransferCovarianceMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkFreeModule DPGroupCohomologyHomogeneousPaths
  DPGroupCohomologyHomogeneousMaps DPGroupCohomologyHomogeneousComplex
  DPGroupCohomologyHomogeneousEquivariance DPGroupCohomologyHomogeneousCohomology
  DPGroupCohomologyTransferCosets DPGroupCohomologyTransferHomogeneous
  DPGroupCohomologyHomogeneousSemilinear DPGroupCohomologyCosetSumsCovariance
  DPGroupCohomologyCosetSums DPGroupCohomologyTransferCovarianceMaps.
Local Open Scope ring_scope.
Local Open Scope group_scope.

Module DPGroupCohomologyTransferCovarianceCochains.
Section Covariance.
Variable R : comPzRingType.
Variables G K : finGroupType.
Variables P Q : {group G}.
Hypothesis hPQ : P \subset Q.
Variable e : {morphism Q >-> K}.
Hypothesis he : 'injm e.
Variable A : lmodType R.
Local Notation PI := (e @* P)%G.
Local Notation QI := (e @* Q)%G.
Local Notation phi := (vertex_map e).

Definition lower_cochain := @ambient_semilinear R G K P PI (lower_hom hPQ e)
  phi (vertex_map_lower_equivariant hPQ e) A.
Definition upper_cochain := @ambient_semilinear R G K Q QI (upper_hom e)
  phi (vertex_map_upper_equivariant e) A.

Lemma vertex_action n t (ht : t \in Q) (v : homogeneous_term R G n) :
  homogeneous_map R phi n (homogeneous_action R n t v) =
    homogeneous_action R n (e t) (homogeneous_map R phi n v).
Proof.
have h := @semilinear_action R G K Q QI (upper_hom e) phi
  (vertex_map_upper_equivariant e) n (Sub t ht) v.
exact h.
Qed.

Theorem ambient_transfer_covariance n
    (f : cochain_term (@ambient_hom_complex R K PI A) n) :
  cochain_map_at (@ambient_transfer R G P Q A) n
      (cochain_map_at lower_cochain n f) =
    cochain_map_at upper_cochain n
      (cochain_map_at (@ambient_transfer R K PI QI A) n f).
Proof.
apply diagram_hom_ext => x v.
change (coset_sum P Q (fun t => module_hom_fun (component f tt)
    (homogeneous_map R phi n (homogeneous_action R n t v))) =
  coset_sum PI QI (fun t => module_hom_fun (component f tt)
    (homogeneous_action R n t (homogeneous_map R phi n v)))).
have hinv : left_invariant PI (fun t => module_hom_fun (component f tt)
    (homogeneous_action R n t (homogeneous_map R phi n v))).
  move=> p hp t; rewrite homogeneous_action_composition.
  exact: ambient_functional_invariant.
rewrite -(coset_sum_covariance hPQ he hinv).
apply: eq_bigr=> C hC.
have ht : repr C \in Q := coset_representative_mem hPQ (Sub C hC).
by rewrite vertex_action.
Qed.

Theorem ambient_transfer_covariance_cohomology n
    (z : cohomology (@ambient_hom_complex R K PI A) n) :
  cohomology_map (@ambient_transfer R G P Q A) n
      (cohomology_map lower_cochain n z) =
    cohomology_map upper_cochain n
      (cohomology_map (@ambient_transfer R K PI QI A) n z).
Proof.
have [w <-] := quotient_pi_surjective z.
rewrite !cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; exact: ambient_transfer_covariance.
Qed.

End Covariance.
End DPGroupCohomologyTransferCovarianceCochains.
