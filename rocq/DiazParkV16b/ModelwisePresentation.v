(** Genuine model-generator freeness, with actual natural extensions and uniqueness. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPModelwisePresentation.
Section Presentation.
Variable R : pzRingType.
Variable C : category.
Variable I : Type.
Variable models : I -> C.
Variable P : module_diagram R C.
Record model_presentation := ModelPresentation {
  model_generator : forall i, fobj P (models i);
  model_lift : forall (F : module_diagram R C), (forall i, fobj F (models i)) -> nat_trans P F;
  model_lift_generator : forall (F : module_diagram R C) (x : forall i, fobj F (models i)) i,
    module_hom_fun (component (@model_lift F x) (models i)) (model_generator i) = x i;
  model_hom_ext : forall (F : module_diagram R C) (a b : nat_trans P F),
    (forall i, module_hom_fun (component a (models i)) (model_generator i) =
      module_hom_fun (component b (models i)) (model_generator i)) -> a = b
}.

Variable p : model_presentation.
Variables F G : module_diagram R C.
Variable tau : nat_trans F G.
Variable c : nat_trans P G.
Variable hpre : forall i, exists x : fobj F (models i),
  module_hom_fun (component tau (models i)) x = module_hom_fun (component c (models i)) (model_generator p i).

Definition lift_along_choice i := proj1_sig (constructive_indefinite_description (hpre i)).
Definition lift_along : nat_trans P F := model_lift p (fun i => lift_along_choice i).

Lemma lift_along_generator i : module_hom_fun (component lift_along (models i)) (model_generator p i) = lift_along_choice i.
Proof. exact: model_lift_generator. Qed.

Theorem lift_along_comp : nat_comp lift_along tau = c.
Proof.
apply (@model_hom_ext p G (nat_comp lift_along tau) c) => i.
change (module_hom_fun (component tau (models i))
  (module_hom_fun (component lift_along (models i)) (model_generator p i)) =
  module_hom_fun (component c (models i)) (model_generator p i)).
rewrite lift_along_generator; exact (proj2_sig (constructive_indefinite_description (hpre i))).
Qed.
Lemma lift_along_apply (X : C) (x : fobj P X) :
  module_hom_fun (component tau X) (module_hom_fun (component lift_along X) x) =
  module_hom_fun (component c X) x.
Proof. exact (f_equal (fun t : nat_trans P G => module_hom_fun (component t X) x) lift_along_comp). Qed.
End Presentation.
End DPModelwisePresentation.
