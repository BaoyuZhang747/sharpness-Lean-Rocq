(** The actual contravariant module diagram of a Mackey pair. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules MackeyPair.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Definition pair_codiagram (R : comPzRingType) (C : category)
    (M : mackey_pair R C) : module_codiagram R C.
Proof.
  refine (@Build_functor (opposite C) (module_category R) (pair_value M)
    (fun P Q f => module_hom_of_linear (pair_pull M f)) _ _).
  - intro P. apply module_hom_ext. intro x. exact (@pair_pull_id R C M P x).
  - intros P Q T f g. apply module_hom_ext. intro x.
    exact (@pair_pull_comp R C M T Q P g f x).
Defined.

Definition pair_restrict (R : comPzRingType) (C D : category)
    (M : mackey_pair R D) (L : functor C D) : mackey_pair R C.
Proof.
  refine (@MackeyPair R C (fun P => pair_value M (fobj L P))
    (fun P Q f => pair_pull M (fmap L f))
    (fun P Q f => pair_push M (fmap L f)) _ _ _ _ _).
  - intros P x. rewrite fmap_id. exact (@pair_pull_id R D M _ x).
  - intros P x. rewrite fmap_id. exact (@pair_push_id R D M _ x).
  - intros P Q T f g x. rewrite fmap_compose. apply pair_pull_comp.
  - intros P Q T f g x. rewrite fmap_compose. apply pair_push_comp.
  - intros P Q e x. exact (@pair_pull_iso R D M _ _ (functor_iso L e) x).
Defined.
