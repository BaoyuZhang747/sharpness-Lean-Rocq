(** An actual split injection of free modules for any injective map of sets. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import BarFreeModule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule.
Local Open Scope ring_scope.

Module DPFreeModuleEmbeddings.
Section Embedding.
Variable R : pzRingType.
Variables X Y : Type.
Variable f : X -> Y.
Hypothesis hf : injective f.

Definition inverse_basis (y : Y) : free_module R X :=
  match pselect (exists x, f x = y) with
  | left h => free_basis R (proj1_sig (constructive_indefinite_description h))
  | right _ => 0
  end.

Lemma inverse_basis_image x : inverse_basis (f x) = free_basis R x.
Proof.
rewrite /inverse_basis; case: (pselect (exists z, f z = f x)) => [h|h].
- have e : proj1_sig (constructive_indefinite_description h) = x.
    apply hf; exact (proj2_sig (constructive_indefinite_description h)).
  by rewrite e.
- exfalso; apply h; by exists x.
Qed.

Definition free_map_retraction : {linear free_module R Y -> free_module R X} :=
  (free_lift inverse_basis : {linear _ -> _}).

Lemma free_map_retraction_cancel (a : free_module R X) :
  free_map_retraction (free_map R f a) = a.
Proof.
apply (free_lift_ext
  (g := (free_map_retraction \o free_map R f : {linear _ -> _}))
  (h := (idfun : {linear free_module R X -> free_module R X}))).
move=> x; rewrite /= free_map_basis /free_map_retraction free_lift_basis.
exact: inverse_basis_image.
Qed.

Theorem free_map_injective : injective (free_map R f).
Proof.
move=> a b h; rewrite -(free_map_retraction_cancel a) -(free_map_retraction_cancel b).
by rewrite h.
Qed.
End Embedding.
End DPFreeModuleEmbeddings.
