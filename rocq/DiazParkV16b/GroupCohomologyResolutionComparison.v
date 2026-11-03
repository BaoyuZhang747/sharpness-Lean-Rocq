(** A specified augmentation-preserving comparison of actual projective
    resolutions induces an isomorphism, with that literal forward map. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryEnoughProjectivesResolution
  CategoryEnoughProjectivesComparison CategoryEnoughProjectivesComparisonHomotopy
  ProjectiveExtComplex ProjectiveExtIndependence HomologicalCohomology
  HomologicalCohomologyMaps MackeyModuleCarriers MackeyModuleQuotient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPEnoughProjectiveResolutions DPProjectiveComparison DPProjectiveHomotopy
  DPProjectiveExt DPProjectiveExtIndependence DiazParkCohomology DiazParkCohomologyMaps.

Module DPGroupCohomologyResolutionComparison.
Section Comparison.
Variables (R : comPzRingType) (C : category).
Variables A D : module_diagram R C.
Variables P Q : projective_resolution A.
Variable f : projective_resolution_map P Q (nat_id A).

Definition specified_comparison_iso n : @isomorphism (module_category R)
    [the lmodType R of cohomology (projective_hom_complex Q D) n]
    [the lmodType R of cohomology (projective_hom_complex P D) n].
Proof.
pose g := projective_resolution_comparison Q P (nat_id A).
refine (@Build_isomorphism (module_category R) _ _
  (module_hom_of_linear (cohomology_map (projective_hom_map D f) n))
  (module_hom_of_linear (cohomology_map (projective_hom_map D g) n)) _ _).
- apply module_hom_ext => q; exact: (@projective_hom_inverse R C A D Q P g f n q).
- apply module_hom_ext => q; exact: (@projective_hom_inverse R C A D P Q f g n q).
Defined.

Lemma specified_comparison_iso_hom n :
  iso_hom (specified_comparison_iso n) =
    module_hom_of_linear (cohomology_map (projective_hom_map D f) n).
Proof. reflexivity. Qed.

Lemma specified_comparison_independent
    (g : projective_resolution_map P Q (nat_id A)) n :
  module_hom_of_linear (cohomology_map (projective_hom_map D f) n) =
    module_hom_of_linear (cohomology_map (projective_hom_map D g) n).
Proof.
apply module_hom_ext => q.
exact: (projective_hom_maps_equal (D := D) (projective_resolution_maps_homotopic f g) q).
Qed.

End Comparison.
End DPGroupCohomologyResolutionComparison.
