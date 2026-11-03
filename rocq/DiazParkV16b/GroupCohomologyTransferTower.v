(** The actual native transfers are transitive through every subgroup tower. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness
  CategoryDiagramHom HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import GroupCohomologyHomogeneousComplex
  GroupCohomologyHomogeneousEquivariance GroupCohomologyHomogeneousCohomology
  GroupCohomologyTransferCosets GroupCohomologyTransferHomogeneous GroupCohomologyTransferNative
  GroupCohomologyCosetSumsTower.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DPGroupCohomologyHomogeneousComplex DPGroupCohomologyHomogeneousEquivariance
  DPGroupCohomologyHomogeneousCohomology DPGroupCohomologyTransferCosets
  DPGroupCohomologyTransferHomogeneous DPGroupCohomologyTransferNative
  DPGroupCohomologyCosetSumsTower.

Module DPGroupCohomologyTransferTower.
Section Tower.
Variable R : comPzRingType.
Variable G : finGroupType.
Variables P Q T : {group G}.
Variables (hPQ : P \subset Q) (hQT : Q \subset T).
Variable A : lmodType R.

Lemma ambient_transfer_tower n (f : cochain_term (@ambient_hom_complex R G P A) n) :
  cochain_map_at (@ambient_transfer R G P T A) n f =
    cochain_map_at (@ambient_transfer R G Q T A) n
      (cochain_map_at (@ambient_transfer R G P Q A) n f).
Proof.
apply diagram_hom_ext => x v.
have hinv : left_invariant P (fun t =>
    module_hom_fun (component f tt) (homogeneous_action R n t v)).
  move=> p hp t; rewrite homogeneous_action_composition.
  exact: ambient_functional_invariant.
change (coset_sum P T (fun t => module_hom_fun (component f tt)
    (homogeneous_action R n t v)) =
  coset_sum Q T (fun t => coset_sum P Q (fun q => module_hom_fun (component f tt)
    (homogeneous_action R n q (homogeneous_action R n t v))))).
rewrite (coset_sum_tower hPQ hQT hinv).
apply: eq_bigr => C hC; apply: eq_bigr => D hD.
by rewrite homogeneous_action_composition.
Qed.

Lemma ambient_transfer_cohomology_tower n (q : cohomology (@ambient_hom_complex R G P A) n) :
  cohomology_map (@ambient_transfer R G P T A) n q =
    cohomology_map (@ambient_transfer R G Q T A) n
      (cohomology_map (@ambient_transfer R G P Q A) n q).
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; exact: ambient_transfer_tower.
Qed.

Theorem transfer_tower n :
  transfer A (subset_trans hPQ hQT) n =
    module_hom_comp (transfer A hPQ n) (transfer A hQT n).
Proof.
apply module_hom_ext => q.
change (module_hom_fun (iso_hom (@ambient_native_iso R G T A n))
    (cohomology_map (@ambient_transfer R G P T A) n
      (module_hom_fun (iso_inv (@ambient_native_iso R G P A n)) q)) =
  module_hom_fun (iso_hom (@ambient_native_iso R G T A n))
    (cohomology_map (@ambient_transfer R G Q T A) n
      (module_hom_fun (iso_inv (@ambient_native_iso R G Q A n))
        (module_hom_fun (iso_hom (@ambient_native_iso R G Q A n))
          (cohomology_map (@ambient_transfer R G P Q A) n
            (module_hom_fun (iso_inv (@ambient_native_iso R G P A n)) q)))))).
by rewrite module_iso_hom_inv_apply ambient_transfer_cohomology_tower.
Qed.

End Tower.
End DPGroupCohomologyTransferTower.
