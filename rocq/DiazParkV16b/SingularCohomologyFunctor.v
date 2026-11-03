(** Actual contravariant singular cohomology functor on topological spaces. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category CategoryModules HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import TopologicalCategory SingularSet SingularCohomology
  CochainMapsLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularSet DPSingularCohomology DPCochainMapsLaws
  DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.

Module DPSingularCohomologyFunctor.
Section Functor.
Variable Real : realType.
Variable R : pzRingType.
Variable A : lmodType R.
Variable n : nat.

Lemma singular_cohomology_identity (X : topologicalType)
    (q : singular_cohomology Real X A n) :
  singular_cohomology_map Real (@identity topological_category X) A n q = q.
Proof.
apply cohomology_identity_of => a.
apply functional_extensionality_dep => s.
change (a (compose s (@identity topological_category X)) = a s).
by rewrite compose_id_right.
Qed.

Lemma singular_cohomology_composition (X Y Z : topologicalType)
    (f : hom topological_category X Y) (g : hom topological_category Y Z)
    (q : singular_cohomology Real Z A n) :
  singular_cohomology_map Real (compose f g) A n q =
    singular_cohomology_map Real f A n (singular_cohomology_map Real g A n q).
Proof.
apply cohomology_composition_of => a.
apply functional_extensionality_dep => s.
change (a (compose s (compose f g)) = a (compose (compose s f) g)).
by rewrite compose_assoc.
Qed.

Definition singular_cohomology_functor : functor (opposite topological_category) (module_category R).
Proof.
refine (@Build_functor (opposite topological_category) (module_category R)
  (fun X => [the lmodType R of cohomology (singular_cochains Real X A) n])
  (fun X Y f => module_hom_of_linear (singular_cohomology_map Real f A n)) _ _).
- move=> X; apply module_hom_ext => q; exact: singular_cohomology_identity.
- move=> X Y Z f g; apply module_hom_ext => q; exact: singular_cohomology_composition.
Defined.
End Functor.
End DPSingularCohomologyFunctor.
