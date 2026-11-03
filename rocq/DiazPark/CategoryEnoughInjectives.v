(** Unconditional existence of injective diagram embeddings and augmented
    injective resolutions. The module-existence theorem is proved from the
    actual divisible envelope and coinduction construction. *)
From mathcomp Require Import ssralg.
From DiazPark Require Import Category CategoryModules CategoryExtensionality
  CategoryInjectives CategoryDiagramEnoughInjectives CategoryInjectiveResolution
  ModuleEnoughInjectives.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition chosen_diagram_injective_embedding (R : pzRingType)
    {C : category} (F : module_diagram R C) : diagram_injective_embedding F :=
  @diagram_injective_embedding_from_modules R (@module_enough_injectives R) C F.

Arguments chosen_diagram_injective_embedding R {C} F.

Theorem diagram_enough_injectives (R : pzRingType) {C : category}
    (F : module_diagram R C) :
    exists (J : module_diagram R C) (m : nat_trans F J),
      @monomorphism (functor_category C (module_category R)) F J m /\
      injective_object (functor_category C (module_category R)) J.
Proof.
  pose (e := chosen_diagram_injective_embedding R F).
  exists (diagram_embedding_target e), (diagram_embedding_map e).
  split; [exact (@diagram_embedding_monomorphism R C F e) | exact (diagram_embedding_injective e)].
Qed.

Definition chosen_injective_resolution (R : pzRingType) {C : category}
    (F : module_diagram R C) : injective_resolution F :=
  injective_resolution_from_embeddings (fun G => chosen_diagram_injective_embedding R G) F.

Arguments chosen_diagram_injective_embedding R {C} F.
Arguments chosen_injective_resolution R {C} F.
