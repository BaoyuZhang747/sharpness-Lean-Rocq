(** The constructed pair has precisely the independently defined native
    ordinary-cohomology coefficient, including every orbit arrow. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryIsomorphism CategoryModules
  MackeyPairDiagrams FusionSystems FusionOrbit.
From DiazParkV16b Require Import GroupCohomologyOrbitCoefficient GroupCohomologyMackeyPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomologyOrbitCoefficient DPGroupCohomologyMackeyPair.

Module DPGroupCohomologyMackeyDiagram.
Section Diagram.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.

Theorem native_pair_codiagram :
  pair_codiagram (native_cohomology_pair F A n) = coefficient F A n.
Proof.
apply (@functor_extensionality (opposite (DPFusionOrbit.orbit_category F))
  (module_category R) (pair_codiagram (native_cohomology_pair F A n))
  (coefficient F A n) (Logic.eq_refl _)).
apply functional_extensionality_dep => P.
apply functional_extensionality_dep => Q.
apply functional_extensionality_dep => a.
apply module_hom_ext => z; reflexivity.
Qed.

Theorem native_centric_pair_codiagram :
  pair_codiagram (pair_restrict (native_cohomology_pair F A n)
    (DPFusionOrbit.centric_inclusion F)) = centric_coefficient F A n.
Proof.
apply (@functor_extensionality (opposite (DPFusionOrbit.centric_orbit_category F))
  (module_category R)
  (pair_codiagram (pair_restrict (native_cohomology_pair F A n)
    (DPFusionOrbit.centric_inclusion F)))
  (centric_coefficient F A n) (Logic.eq_refl _)).
apply functional_extensionality_dep => P.
apply functional_extensionality_dep => Q.
apply functional_extensionality_dep => a.
apply module_hom_ext => z; reflexivity.
Qed.

End Diagram.
End DPGroupCohomologyMackeyDiagram.


