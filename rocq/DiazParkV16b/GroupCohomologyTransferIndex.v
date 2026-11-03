(** Restriction followed by actual transfer multiplies by the subgroup index. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness
  CategoryDiagramHom HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyPullback
  GroupCohomologyHomogeneousComplex GroupCohomologyHomogeneousEquivariance
  GroupCohomologyHomogeneousCohomology GroupCohomologyHomogeneousRestriction
  GroupCohomologyTransferCosets GroupCohomologyTransferHomogeneous
  GroupCohomologyTransferNative GroupCohomologyCosetSumsTowerCoordinates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DPGroupCohomologyPullback
  DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DPGroupCohomologyHomogeneousComplex DPGroupCohomologyHomogeneousEquivariance
  DPGroupCohomologyHomogeneousCohomology DPGroupCohomologyHomogeneousRestriction
  DPGroupCohomologyTransferCosets DPGroupCohomologyTransferHomogeneous
  DPGroupCohomologyTransferNative DPGroupCohomologyCosetSums.
Local Open Scope ring_scope.

Module DPGroupCohomologyTransferIndex.
Section Index.
Variable R : comPzRingType.
Variable G : finGroupType.
Variables P Q : {group G}.
Variable h : P \subset Q.
Variable A : lmodType R.

Lemma ambient_transfer_restriction_index n
    (f : cochain_term (@ambient_hom_complex R G Q A) n) :
  cochain_map_at (@ambient_transfer R G P Q A) n
    (cochain_map_at (@ambient_restriction R G P Q h A) n f) = f *+ (indexg Q P).
Proof.
apply diagram_hom_ext => x v; case: x v => v.

change (coset_sum P Q (fun t => module_hom_fun (component f tt)
    (homogeneous_action R n t v)) =
  module_hom_fun (component (f *+ (indexg Q P)) tt) v).
transitivity (\sum_(C in rcosets P Q) module_hom_fun (component f tt) v).
- apply: eq_bigr => C hC.
  have hm : repr C \in Q := coset_representative_mem h (Sub C hC : coset_type P Q).
  exact (@ambient_functional_invariant R G Q A n f (repr C) hm v).
- rewrite sumr_const.
  change (diagram_hom_at f tt v *+ (indexg Q P) =
    diagram_hom_at (f *+ (indexg Q P)) tt v).
  elim: (indexg Q P) => [|m IH]; first reflexivity.
  by rewrite !mulrS diagram_hom_at_add IH.
Qed.

Lemma ambient_transfer_restriction_cohomology_index n
    (q : cohomology (@ambient_hom_complex R G Q A) n) :
  cohomology_map (@ambient_transfer R G P Q A) n
    (cohomology_map (@ambient_restriction R G P Q h A) n q) = q *+ (indexg Q P).
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !cohomology_map_pi -linearMn; congr (quotient_pi _ _).
apply submodule_val_injective.
change (cochain_map_at (@ambient_transfer R G P Q A) n
    (cochain_map_at (@ambient_restriction R G P Q h A) n (submodule_val z)) =
  submodule_val (z *+ (indexg Q P))).
rewrite ambient_transfer_restriction_index.
change (val z *+ indexg Q P = val (z *+ indexg Q P)).
by rewrite linearMn.
Qed.

Theorem transfer_restriction_index n (q : value R [the finGroupType of [subg Q]] A n) :
  module_hom_fun (transfer A h n)
    (module_hom_fun (pull A (subgroup_nested_hom h) n) q) = q *+ (indexg Q P).
Proof.
pose eP := @ambient_native_iso R G P A n.
pose eQ := @ambient_native_iso R G Q A n.
have [a ha] : exists a, module_hom_fun (iso_hom eQ) a = q.
  exists (module_hom_fun (iso_inv eQ) q); exact: module_iso_inv_hom_apply.
rewrite -ha.
have hs := congr1 (fun k => module_hom_fun k a)
  (@ambient_restriction_native_cohomology_square R G P Q h A n).
change (module_hom_fun (iso_hom eP)
    (cohomology_map (@ambient_restriction R G P Q h A) n a) =
  module_hom_fun (pull A (subgroup_nested_hom h) n)
    (module_hom_fun (iso_hom eQ) a)) in hs.
rewrite -hs.
change (module_hom_fun (iso_hom eQ)
    (cohomology_map (@ambient_transfer R G P Q A) n
      (module_hom_fun (iso_inv eP) (module_hom_fun (iso_hom eP)
        (cohomology_map (@ambient_restriction R G P Q h A) n a)))) =
  module_hom_fun (iso_hom eQ) a *+ (indexg Q P)).
rewrite module_iso_hom_inv_apply ambient_transfer_restriction_cohomology_index.
elim: (indexg Q P) => [|m IH]; first exact: module_hom_zero.
by rewrite !mulrS module_hom_add IH.
Qed.

End Index.
End DPGroupCohomologyTransferIndex.



