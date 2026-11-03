(** Actual constant-coefficient cohomology of the costructured categories,
    with the literal functor pullbacks induced by postcomposition. *)
From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category CategoryComma CategoryModules.
From DiazParkV16b Require Import CategoryCostructuredDiagram CategoryConstantCohomology.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCategoryCostructuredDiagram.

Module DPCategoryCostructuredCohomologyDiagram.
Section Diagram.
Variable R : pzRingType.
Variable A : lmodType R.
Variables C D : category.
Variable T : functor C D.
Variable n : nat.

Definition coefficient : module_codiagram R D.
Proof.
refine (@Build_functor (opposite D) (module_category R)
  (fun d => DPCategoryConstantCohomology.value R A (costructured_category T d) n)
  (fun d e f => DPCategoryConstantCohomology.pull A (reindex T f) n) _ _).
- move=> d; rewrite reindex_id DPCategoryConstantCohomology.pull_identity; reflexivity.
- move=> d e k f g; rewrite reindex_comp DPCategoryConstantCohomology.pull_composition; reflexivity.
Defined.

Lemma coefficient_object (d : D) :
    fobj coefficient d = DPCategoryConstantCohomology.value R A (costructured_category T d) n.
Proof. reflexivity. Qed.

Lemma coefficient_map (d e : D) (f : hom D d e) :
    @fmap _ _ coefficient e d f = DPCategoryConstantCohomology.pull A (reindex T f) n.
Proof. reflexivity. Qed.
End Diagram.
End DPCategoryCostructuredCohomologyDiagram.
