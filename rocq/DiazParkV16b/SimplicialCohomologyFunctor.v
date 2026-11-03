(** Actual contravariant function-cochain cohomology on simplicial sets. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category CategoryModules HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import SimplicialSet SimplicialSetYoneda SimplicialCochains SimplicialCochainMaps CochainMapsLaws.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DPSimplicialSet DPSimplicialYoneda DPSimplicialCochains DPSimplicialCochainMaps DPCochainMapsLaws.
Module DPSimplicialCohomologyFunctor.
Section Functor.
Variable R:pzRingType.
Variable A:lmodType R.
Variable n:nat.
Lemma simplicial_cohomology_identity X (x:cohomology (complex X A) n) :
 cohomology_map (pull (nat_id X) A) n x=x.
Proof. apply cohomology_identity_of; exact: pull_identity. Qed.
Lemma simplicial_cohomology_composition X Y Z (f:simplicial_map X Y) (g:simplicial_map Y Z)
 (x:cohomology (complex Z A) n) : cohomology_map (pull (nat_comp f g) A) n x=
 cohomology_map (pull f A) n (cohomology_map (pull g A) n x).
Proof. apply cohomology_composition_of; exact: pull_composition. Qed.
Definition simplicial_cohomology_functor : functor (opposite simplicial_category) (module_category R).
Proof.
refine (@Build_functor (opposite simplicial_category) (module_category R)
 (fun X=>[the lmodType R of cohomology (complex X A) n])
 (fun X Y f=>module_hom_of_linear (cohomology_map (pull f A) n)) _ _).
- move=>X; apply module_hom_ext=>x; exact: simplicial_cohomology_identity.
- move=>X Y Z f g; apply module_hom_ext=>x; exact: simplicial_cohomology_composition.
Defined.
Definition simplicial_cohomology_diagram (C:category) (F:functor C simplicial_category) :=
 functor_comp (functor_op F) simplicial_cohomology_functor.
End Functor.
End DPSimplicialCohomologyFunctor.
