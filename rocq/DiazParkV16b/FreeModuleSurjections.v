(** The actual free-module functor sends a surjection of generators to a surjection. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import BarFreeModule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule.
Local Open Scope ring_scope.
Module DPFreeModuleSurjections.
Section Surjection.
Variable R : pzRingType.
Variables X Y : Type.
Variable f : X -> Y.
Variable hf : forall y, exists x, f x = y.

Definition generator_preimage y :=
  proj1_sig (constructive_indefinite_description (hf y)).
Lemma generator_preimage_equation y : f (generator_preimage y) = y.
Proof. exact: (proj2_sig (constructive_indefinite_description (hf y))). Qed.

Lemma free_map_preimage_equation (y : free_module R Y) :
  free_map R f (free_map R generator_preimage y) = y.
Proof.
apply: (free_lift_ext
  (g := (free_map R f \o free_map R generator_preimage : {linear _ -> _}))
  (h := (idfun : {linear free_module R Y -> free_module R Y}))).
move=> x; by rewrite /= !free_map_basis generator_preimage_equation.
Qed.

Theorem free_map_surjective (y : free_module R Y) : exists x, free_map R f x = y.
Proof. exists (free_map R generator_preimage y); exact: free_map_preimage_equation. Qed.
End Surjection.
End DPFreeModuleSurjections.
