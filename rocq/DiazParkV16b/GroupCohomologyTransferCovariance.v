(** Native ordinary-cohomology transfer covariance, obtained from the actual
    common normalized vertex map and the proved right-coset reindexing. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyPullback
  GroupCohomologyHomogeneousCohomology GroupCohomologyTransferHomogeneous
  GroupCohomologyTransferNative GroupCohomologyHomogeneousSemilinear
  GroupCohomologyTransferCovarianceMaps GroupCohomologyTransferCovarianceCochains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DPGroupCohomologyPullback DPGroupCohomologyHomogeneousCohomology
  DPGroupCohomologyTransferHomogeneous DPGroupCohomologyTransferNative
  DPGroupCohomologyHomogeneousSemilinear DPGroupCohomologyTransferCovarianceMaps
  DPGroupCohomologyTransferCovarianceCochains.
Local Open Scope group_scope.

Module DPGroupCohomologyTransferCovariance.
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

Lemma lower_native_square n z :
  module_hom_fun (pull A (lower_hom hPQ e) n)
      (module_hom_fun (iso_hom (@ambient_native_iso R K PI A n)) z) =
    module_hom_fun (iso_hom (@ambient_native_iso R G P A n))
      (cohomology_map (lower_cochain hPQ e A) n z).
Proof.
symmetry.
exact (congr1 (fun f => module_hom_fun f z)
  (@ambient_semilinear_native_cohomology_square R G K P PI
    (lower_hom hPQ e) (vertex_map e) (vertex_map_lower_equivariant hPQ e)
    A (vertex_map_lower_normalized hPQ e) n)).
Qed.

Lemma upper_native_square n z :
  module_hom_fun (pull A (upper_hom e) n)
      (module_hom_fun (iso_hom (@ambient_native_iso R K QI A n)) z) =
    module_hom_fun (iso_hom (@ambient_native_iso R G Q A n))
      (cohomology_map (upper_cochain e A) n z).
Proof.
symmetry.
exact (congr1 (fun f => module_hom_fun f z)
  (@ambient_semilinear_native_cohomology_square R G K Q QI
    (upper_hom e) (vertex_map e) (vertex_map_upper_equivariant e)
    A (vertex_map_upper_normalized e) n)).
Qed.

Theorem transfer_covariance_image n :
  module_hom_comp (pull A (lower_hom hPQ e) n) (transfer A hPQ n) =
    module_hom_comp (transfer A (morphimS e hPQ) n) (pull A (upper_hom e) n).
Proof.
apply module_hom_ext => z.
pose w := module_hom_fun (iso_inv (@ambient_native_iso R K PI A n)) z.
have hz : z = module_hom_fun (iso_hom (@ambient_native_iso R K PI A n)) w.
  symmetry; exact: module_iso_inv_hom_apply.
change (module_hom_fun (transfer A hPQ n)
    (module_hom_fun (pull A (lower_hom hPQ e) n) z) =
  module_hom_fun (pull A (upper_hom e) n)
    (module_hom_fun (transfer A (morphimS e hPQ) n) z)).
rewrite hz lower_native_square.
have hs := congr1 (fun f => module_hom_fun f
  (cohomology_map (lower_cochain hPQ e A) n w))
  (@transfer_ambient_square R G A P Q hPQ n).
have ht := congr1 (fun f => module_hom_fun f w)
  (@transfer_ambient_square R K A PI QI (morphimS e hPQ) n).
change (module_hom_fun (transfer A hPQ n)
    (module_hom_fun (iso_hom (@ambient_native_iso R G P A n))
      (cohomology_map (lower_cochain hPQ e A) n w)) =
  module_hom_fun (iso_hom (@ambient_native_iso R G Q A n))
    (cohomology_map (@ambient_transfer R G P Q A) n
      (cohomology_map (lower_cochain hPQ e A) n w))) in hs.
change (module_hom_fun (transfer A (morphimS e hPQ) n)
    (module_hom_fun (iso_hom (@ambient_native_iso R K PI A n)) w) =
  module_hom_fun (iso_hom (@ambient_native_iso R K QI A n))
    (cohomology_map (@ambient_transfer R K PI QI A) n w)) in ht.
rewrite hs ht upper_native_square.
congr (module_hom_fun _ _).
exact: ambient_transfer_covariance_cohomology.
Qed.

End Covariance.
End DPGroupCohomologyTransferCovariance.
