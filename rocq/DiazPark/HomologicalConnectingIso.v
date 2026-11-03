From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category CategoryModules HomologicalComplex HomologicalCohomology
  HomologicalConnecting HomologicalModuleIso MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology
  DiazParkHomologicalConnecting DiazParkHomologicalModuleIso.

Module DiazParkHomologicalConnectingIso.
Section Iso.
Variable R : pzRingType.
Variables A B C : @cochain_complex R.
Variables (f : cochain_map A B) (g : cochain_map B C).
Variable s : degreewise_short_exact f g.
Variable hB : positive_acyclic B.

Definition positive_connecting_iso n : @isomorphism (module_category R)
    [the lmodType R of cohomology C n.+1] [the lmodType R of cohomology A n.+2].
Proof.
apply: (@linear_bijection_iso R _ _ (connecting_map s n.+1)).
- apply: connecting_map_injective.
  exact: (proj1 (positive_acyclic_cohomology B) hB n).
- apply: connecting_map_surjective; exact (@hB n.+1).
Defined.

End Iso.
End DiazParkHomologicalConnectingIso.


