(** Chosen injective embeddings of actual arbitrary module diagrams.
    The construction below reduces only the existence of injective module
    embeddings to the explicit coinduced-diagram construction. The final
    unconditional specialization is added after ModuleEnoughInjectives. *)
From mathcomp Require Import all_ssreflect ssralg boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryInjectives ModuleInjectives ModuleDiagrams CategoryDiagramInjectives.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record diagram_injective_embedding {R : pzRingType} {C : category}
    (F : module_diagram R C) := {
  diagram_embedding_target : module_diagram R C;
  diagram_embedding_map : nat_trans F diagram_embedding_target;
  diagram_embedding_pointwise_injective : forall x,
    injective (module_hom_fun (component diagram_embedding_map x));
  diagram_embedding_injective :
    injective_object (functor_category C (module_category R)) diagram_embedding_target
}.

Arguments diagram_embedding_target {R C F} _.
Arguments diagram_embedding_map {R C F} _.
Arguments diagram_embedding_pointwise_injective {R C F} _ x.
Arguments diagram_embedding_injective {R C F} _.

Lemma diagram_embedding_monomorphism {R : pzRingType} {C : category}
    {F : module_diagram R C} (e : diagram_injective_embedding F) :
    @monomorphism (functor_category C (module_category R)) F
      (diagram_embedding_target e) (diagram_embedding_map e).
Proof. apply pointwise_injective_monomorphism. apply diagram_embedding_pointwise_injective. Qed.

Definition diagram_injective_embedding_from_modules (R : pzRingType)
    (enough : forall A : lmodType R, exists (J : lmodType R) (i : module_hom A J),
      injective i /\ module_injective J)
    {C : category} (F : module_diagram R C) : diagram_injective_embedding F.
Proof.
  pose (J := fun c : C => proj1_sig
    (constructive_indefinite_description (enough (fobj F c)))).
  pose (i := fun c : C => proj1_sig
    (constructive_indefinite_description (proj2_sig
      (constructive_indefinite_description (enough (fobj F c)))))).
  assert (hi : forall c, injective (i c)).
  { intro c. exact (proj1 (proj2_sig (constructive_indefinite_description
      (proj2_sig (constructive_indefinite_description (enough (fobj F c))))))). }
  assert (hJ : forall c, module_injective (J c)).
  { intro c. exact (proj2 (proj2_sig (constructive_indefinite_description
      (proj2_sig (constructive_indefinite_description (enough (fobj F c))))))). }
  refine (@Build_diagram_injective_embedding R C F (coinduced_diagram J)
    (coinduced_lift i) _ (coinduced_diagram_injective hJ)).
  exact (@coinduced_lift_pointwise_injective R C J F i hi).
Defined.
