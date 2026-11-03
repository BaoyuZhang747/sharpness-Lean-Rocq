(** The native cohomology diagram of an arbitrary actual cochain diagram. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  HomologicalComplex HomologicalDiagramInjectives CategoryFiberVanishing
  HomologicalCohomology HomologicalCohomologyMaps MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import CochainMapsLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DPCochainMapsLaws.

Section CohomologyDiagram.
Variable R : pzRingType.
Variable C : category.
Variable K : @diagram_complex R C.

Definition diagram_evaluation_arrow {c d : C} (f : hom C c d) :
    cochain_map (diagram_evaluation_complex K c) (diagram_evaluation_complex K d).
Proof.
refine (@CochainMap R (diagram_evaluation_complex K c) (diagram_evaluation_complex K d)
  (fun n => module_hom_to_linear (fmap (diagram_term K n) f)) _).
intros n x.
have h := naturality (diagram_d K n) f.
exact (f_equal (fun g => module_hom_fun g x) h).
Defined.

Lemma diagram_cohomology_identity n c (x : cohomology (diagram_evaluation_complex K c) n) :
    cohomology_map (diagram_evaluation_arrow (identity c)) n x = x.
Proof.
apply cohomology_identity_of; intro a.
change (module_hom_fun (fmap (diagram_term K n) (identity c)) a = a).
by rewrite fmap_id.
Qed.

Lemma diagram_cohomology_composition n c d e (f : hom C c d) (g : hom C d e)
    (x : cohomology (diagram_evaluation_complex K c) n) :
    cohomology_map (diagram_evaluation_arrow (compose f g)) n x =
    cohomology_map (diagram_evaluation_arrow g) n (cohomology_map (diagram_evaluation_arrow f) n x).
Proof.
apply cohomology_composition_of; intro a.
change (module_hom_fun (fmap (diagram_term K n) (compose f g)) a =
  module_hom_fun (fmap (diagram_term K n) g) (module_hom_fun (fmap (diagram_term K n) f) a)).
by rewrite fmap_compose.
Qed.

Definition cochain_cohomology_diagram (n : nat) : module_diagram R C.
Proof.
refine (@Build_functor C (module_category R)
  (fun c => [the lmodType R of cohomology (diagram_evaluation_complex K c) n])
  (fun c d f => module_hom_of_linear (cohomology_map (diagram_evaluation_arrow f) n)) _ _).
- intro c; apply module_hom_ext; exact: diagram_cohomology_identity.
- intros c d e f g; apply module_hom_ext; exact: diagram_cohomology_composition.
Defined.
End CohomologyDiagram.
