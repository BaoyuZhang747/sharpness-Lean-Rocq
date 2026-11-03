From mathcomp Require Import boolp.
From DiazPark Require Import Category CategoryIsomorphism.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialTypes.

(** The ordinary universe-polymorphic category of types and functions. *)
Definition type_category : category.
Proof.
  refine {| object := Type;
            hom := fun A B => A -> B;
            identity := fun A x => x;
            compose := fun A B C f g x => g (f x) |}; reflexivity.
Defined.

Lemma type_morphism_ext (A B : type_category) (f g : hom type_category A B) :
  (forall x, f x = g x) -> f = g.
Proof. apply functional_extensionality_dep. Qed.

End DPSimplicialTypes.
