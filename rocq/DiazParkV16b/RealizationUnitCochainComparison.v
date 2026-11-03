(** Literal characteristic-simplex pullback, its naturality, and arbitrary-module comparison from the actual unit chain quasi-isomorphism. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryComplexIso
 HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import SimplicialSet SimplicialChains SimplicialChainsMaps
 SimplicialCochains SimplicialCochainMaps SimplicialCochainQuasiIso ChainQuasiIsomorphism
 SingularSet SingularCohomology TopologicalCategory GeometricRealizationCarrier GeometricRealizationMaps
 GeometricRealizationSingularAdjunction RealizationUnitChains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
 DPSimplicialSet DPSimplicialChains DPSimplicialChainMaps DPSimplicialCochains DPSimplicialCochainMaps DPSimplicialCochainQuasiIso DPChainQuasiIsomorphism
 DPSingularSet DPSingularCohomology DPTopological DPGeometricRealization DPGeometricRealizationMaps DPGeometricRealizationSingularAdjunction DPRealizationUnitChains.
Module DPRealizationUnitCochainComparison.
Section Unit.
Variable Real:realType.
Variable R:comPzRingType.
Variable A:lmodType R.
Definition unit_pull (X:simplicial_set) : cochain_map
 (singular_cochains Real (realization_space Real X) A) (complex X A) :=
 pull (realization_unit_map Real X) A.

Lemma unit_pull_formula X n (a:cochain_term (singular_cochains Real (realization_space Real X) A) n)
 (x:simplex X n) : cochain_map_at (unit_pull X) n a x=
 a (component (realization_unit_map Real X) n x).
Proof. reflexivity. Qed.

Lemma unit_pull_natural X Y (f:simplicial_map X Y) n
 (a:cochain_term (singular_cochains Real (realization_space Real Y) A) n) :
 cochain_map_at (unit_pull X) n (cochain_map_at (singular_pullback Real (realization_map Real f) A) n a)=
 cochain_map_at (pull f A) n (cochain_map_at (unit_pull Y) n a).
Proof.
apply functional_extensionality_dep=>x.
change (a (component (nat_comp (realization_unit_map Real X) (singular_map Real (realization_map Real f))) n x)=
 a (component (nat_comp f (realization_unit_map Real Y)) n x)).
by rewrite realization_unit_natural.
Qed.

Lemma unit_cohomology_natural X Y (f:simplicial_map X Y) n
 (a:singular_cohomology Real (realization_space Real Y) A n) :
 cohomology_map (unit_pull X) n (singular_cohomology_map Real (realization_map Real f) A n a)=
 cohomology_map (pull f A) n (cohomology_map (unit_pull Y) n a).
Proof.
exact (@cohomology_map_square R _ _ _ _ (singular_pullback Real (realization_map Real f) A) (pull f A)
 (unit_pull Y) (unit_pull X) (@unit_pull_natural X Y f) n a).
Qed.

Variable X:simplicial_set.
Variable hunit:quasi_isomorphism (realization_unit_chains Real R X).
Definition unit_cohomology_iso n : @isomorphism (module_category R)
 [the lmodType R of singular_cohomology Real (realization_space Real X) A n]
 [the lmodType R of cohomology (complex X A) n] :=
 @pull_cohomology_iso R A X (singular_set Real (realization_space Real X)) (realization_unit_map Real X) hunit n.
Theorem unit_cohomology_iso_forward n (x:singular_cohomology Real (realization_space Real X) A n) :
 module_hom_fun (iso_hom (unit_cohomology_iso n)) x=cohomology_map (unit_pull X) n x.
Proof. exact: pull_cohomology_iso_forward. Qed.
End Unit.

Section Coefficients.
Variable Real:realType.
Variable R:comPzRingType.
Variables A B:lmodType R.
Variable u:{linear A -> B}.
Lemma unit_pull_coefficient X n (a:cochain_term (singular_cochains Real (realization_space Real X) A) n) :
 cochain_map_at (coefficient X u) n (cochain_map_at (@unit_pull Real R A X) n a)=
 cochain_map_at (@unit_pull Real R B X) n (cochain_map_at (singular_coefficient_map Real (realization_space Real X) u) n a).
Proof. exact: pull_coefficient. Qed.
Lemma unit_cohomology_coefficient X n (x:singular_cohomology Real (realization_space Real X) A n) :
 cohomology_map (coefficient X u) n (cohomology_map (@unit_pull Real R A X) n x)=
 cohomology_map (@unit_pull Real R B X) n (cohomology_map (singular_coefficient_map Real (realization_space Real X) u) n x).
Proof.
exact (@cohomology_map_square R _ _ _ _ (@unit_pull Real R A X) (@unit_pull Real R B X)
 (singular_coefficient_map Real (realization_space Real X) u) (coefficient X u) (@unit_pull_coefficient X) n x).
Qed.
End Coefficients.
End DPRealizationUnitCochainComparison.
