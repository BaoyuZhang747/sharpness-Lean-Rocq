(** Native transfer on the displayed ordinary cohomology, obtained from the
    actual shared-resolution trace and its proved normalized comparison. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness
  CategoryDiagramHom HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyHomogeneousComplex
  GroupCohomologyHomogeneousEquivariance GroupCohomologyHomogeneousCohomology
  GroupCohomologyTransferCosets GroupCohomologyTransferHomogeneous.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DiazParkHomological DiazParkCohomology
  DiazParkCohomologyMaps DPGroupCohomologyHomogeneousComplex
  DPGroupCohomologyHomogeneousEquivariance DPGroupCohomologyHomogeneousCohomology
  DPGroupCohomologyTransferCosets DPGroupCohomologyTransferHomogeneous.

Module DPGroupCohomologyTransferNative.
Section Native.
Variable R : comPzRingType.
Variable G : finGroupType.
Variable A : lmodType R.

Definition transfer (P Q : {group G}) (_ : P \subset Q) n :
    module_hom (value R [the finGroupType of [subg P]] A n)
      (value R [the finGroupType of [subg Q]] A n) :=
  module_hom_comp (iso_inv (@ambient_native_iso R G P A n))
    (module_hom_comp
      (module_hom_of_linear (cohomology_map (@ambient_transfer R G P Q A) n))
      (iso_hom (@ambient_native_iso R G Q A n))).

Lemma transfer_ambient_square (P Q : {group G}) (h : P \subset Q) n :
  module_hom_comp (iso_hom (@ambient_native_iso R G P A n)) (transfer h n) =
    module_hom_comp
      (module_hom_of_linear (cohomology_map (@ambient_transfer R G P Q A) n))
      (iso_hom (@ambient_native_iso R G Q A n)).
Proof.
apply module_hom_ext => q.
change (module_hom_fun (iso_hom (@ambient_native_iso R G Q A n))
    (cohomology_map (@ambient_transfer R G P Q A) n
      (module_hom_fun (iso_inv (@ambient_native_iso R G P A n))
        (module_hom_fun (iso_hom (@ambient_native_iso R G P A n)) q))) =
  module_hom_fun (iso_hom (@ambient_native_iso R G Q A n))
    (cohomology_map (@ambient_transfer R G P Q A) n q)).
by rewrite module_iso_hom_inv_apply.
Qed.

Lemma ambient_transfer_self (P : {group G}) n
    (f : cochain_term (@ambient_hom_complex R G P A) n) :
  cochain_map_at (@ambient_transfer R G P P A) n f = f.
Proof.
apply diagram_hom_ext => x v; case: x v => v.
change (coset_sum P P (fun t => module_hom_fun (component f tt)
  (homogeneous_action R n t v)) = module_hom_fun (component f tt) v).
rewrite coset_sum_self homogeneous_action_identity.
reflexivity.
Qed.

Lemma ambient_transfer_cohomology_self (P : {group G}) n
    (q : cohomology (@ambient_hom_complex R G P A) n) :
  cohomology_map (@ambient_transfer R G P P A) n q = q.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; exact: ambient_transfer_self.
Qed.

Lemma transfer_self (P : {group G}) (h : P \subset P) n :
  transfer h n = module_hom_id (value R [the finGroupType of [subg P]] A n).
Proof.
apply module_hom_ext => q.
change (module_hom_fun (iso_hom (@ambient_native_iso R G P A n))
    (cohomology_map (@ambient_transfer R G P P A) n
      (module_hom_fun (iso_inv (@ambient_native_iso R G P A n)) q)) = q).
by rewrite ambient_transfer_cohomology_self module_iso_inv_hom_apply.
Qed.

End Native.
Arguments transfer {R G} A {P Q} h n.
End DPGroupCohomologyTransferNative.
