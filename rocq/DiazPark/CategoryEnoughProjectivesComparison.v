(** Actual comparison maps between arbitrary projective resolutions. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  ModuleDiagrams CategoryDiagramImage CategoryDiagramCokernel CategoryEnoughProjectives
  CategoryEnoughProjectivesResolution MackeyModuleCarriers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPEnoughProjectives DPEnoughProjectiveResolutions.
Local Open Scope ring_scope.

Module DPProjectiveComparison.
Section Lifting.
Variables (R : pzRingType) (C : category).
Variables F G P : module_diagram R C.
Variable m : nat_trans F G.
Variable hP : projective_object (functor_category C (module_category R)) P.
Variable t : nat_trans P G.
Hypothesis ht : forall x (v : fobj P x), exists w,
  module_hom_fun (component m x) w = module_hom_fun (component t x) v.

Theorem projective_diagram_factor : exists s : nat_trans P F, nat_comp s m = t.
Proof.
pose k := @subdiagram_lift R C G (diagram_image_subspace m)
  (@diagram_image_stable R C F G m) P t ht.
have hm : @epimorphism (functor_category C (module_category R)) F
    (diagram_image m) (diagram_image_projection m).
  apply pointwise_surjective_epi; exact: diagram_image_projection_surjective.
have [s hs] := @hP _ _ _ hm k.
exists s; apply nat_trans_ext=> x; apply module_hom_ext=> v.
exact (congr1 (fun a : nat_trans P (diagram_image m) =>
  submodule_val (module_hom_fun (component a x) v)) hs).
Qed.
End Lifting.

Record projective_resolution_map {R : pzRingType} {C : category}
    {F G : module_diagram R C} (X : projective_resolution F)
    (Y : projective_resolution G) (u : nat_trans F G) := {
  projective_resolution_map_at : forall n, nat_trans (projective_term X n) (projective_term Y n);
  projective_resolution_map_commutes : forall n x (v : fobj (projective_term X n.+1) x),
    module_hom_fun (component (projective_d Y n) x)
      (module_hom_fun (component (projective_resolution_map_at n.+1) x) v) =
    module_hom_fun (component (projective_resolution_map_at n) x)
      (module_hom_fun (component (projective_d X n) x) v);
  projective_resolution_map_augmentation :
    nat_comp (projective_resolution_map_at 0%N) (projective_augmentation Y) =
      nat_comp (projective_augmentation X) u
}.
Arguments projective_resolution_map_at {R C F G X Y u} _ n.
Arguments projective_resolution_map_commutes {R C F G X Y u} _ n x v.
Arguments projective_resolution_map_augmentation {R C F G X Y u} _.

Section Comparison.
Variables (R : pzRingType) (C : category).
Variables F G : module_diagram R C.
Variables (X : projective_resolution F) (Y : projective_resolution G).
Variable u : nat_trans F G.

Definition comparison_lift_property n
    (f : nat_trans (projective_term X n) (projective_term Y n)) :=
  forall x (v : fobj (projective_term X n.+1) x), exists w,
    module_hom_fun (component (projective_d Y n) x) w =
      module_hom_fun (component f x) (module_hom_fun (component (projective_d X n) x) v).
Arguments comparison_lift_property n f : clear implicits.

Lemma comparison_zero_exists : exists f : nat_trans (projective_term X 0%N) (projective_term Y 0%N),
    nat_comp f (projective_augmentation Y) = nat_comp (projective_augmentation X) u.
Proof.
apply (projective_terms_projective X 0%N).
apply pointwise_surjective_epi; exact: projective_augmentation_surjective.
Qed.
Definition comparison_zero_map := proj1_sig (constructive_indefinite_description comparison_zero_exists).
Lemma comparison_zero_augmentation :
    nat_comp comparison_zero_map (projective_augmentation Y) = nat_comp (projective_augmentation X) u.
Proof. exact (proj2_sig (constructive_indefinite_description comparison_zero_exists)). Qed.
Lemma comparison_zero_lifts : comparison_lift_property 0%N comparison_zero_map.
Proof.
intros x v; apply (proj1 (@projective_exact_augmentation R C G Y x _)).
have h := congr1 (fun a : nat_trans (projective_term X 0%N) G =>
  module_hom_fun (component a x) (module_hom_fun (component (projective_d X 0%N) x) v))
  comparison_zero_augmentation.
transitivity (module_hom_fun (component u x)
  (module_hom_fun (component (projective_augmentation X) x)
    (module_hom_fun (component (projective_d X 0%N) x) v))).
- exact h.
- rewrite projective_augmentation_zero module_hom_zero; reflexivity.
Qed.
Definition comparison_state n :=
  {f : nat_trans (projective_term X n) (projective_term Y n) | comparison_lift_property n f}.
Definition comparison_initial_state : comparison_state 0%N :=
  exist _ comparison_zero_map comparison_zero_lifts.

Lemma comparison_next_exists n (s : comparison_state n) :
    exists f : nat_trans (projective_term X n.+1) (projective_term Y n.+1),
      nat_comp f (projective_d Y n) = nat_comp (projective_d X n) (proj1_sig s) /\
      comparison_lift_property n.+1 f.
Proof.
have [f hf] := @projective_diagram_factor R C (projective_term Y n.+1)
  (projective_term Y n) (projective_term X n.+1) (projective_d Y n)
  (projective_terms_projective X n.+1) (nat_comp (projective_d X n) (proj1_sig s))
  (proj2_sig s).
exists f; split; first exact hf.
intros x v; apply (proj1 (@projective_exact_successor R C G Y n x _)).
have h := congr1 (fun a : nat_trans (projective_term X n.+1) (projective_term Y n) =>
  module_hom_fun (component a x) (module_hom_fun (component (projective_d X n.+1) x) v)) hf.
transitivity (module_hom_fun (component (proj1_sig s) x)
  (module_hom_fun (component (projective_d X n) x)
    (module_hom_fun (component (projective_d X n.+1) x) v))).
- exact h.
- rewrite projective_d_squared module_hom_zero; reflexivity.
Qed.
Definition comparison_next n (s : comparison_state n) : comparison_state n.+1 :=
  exist _ (proj1_sig (constructive_indefinite_description (comparison_next_exists s)))
    (proj2 (proj2_sig (constructive_indefinite_description (comparison_next_exists s)))).
Lemma comparison_next_factor n (s : comparison_state n) :
    nat_comp (proj1_sig (comparison_next s)) (projective_d Y n) =
      nat_comp (projective_d X n) (proj1_sig s).
Proof. exact (proj1 (proj2_sig (constructive_indefinite_description (comparison_next_exists s)))). Qed.
Fixpoint comparison_sequence n : comparison_state n :=
  match n as k return comparison_state k with
  | 0%N => comparison_initial_state
  | k.+1 => comparison_next (comparison_sequence k)
  end.

Definition projective_resolution_comparison : projective_resolution_map X Y u.
Proof.
refine (@Build_projective_resolution_map R C F G X Y u
  (fun n => proj1_sig (comparison_sequence n)) _ comparison_zero_augmentation).
intros n x v.
exact (congr1 (fun a : nat_trans (projective_term X n.+1) (projective_term Y n) =>
  module_hom_fun (component a x) v) (comparison_next_factor (comparison_sequence n))).
Defined.
End Comparison.
Arguments projective_resolution_comparison {R C F G} X Y u.
End DPProjectiveComparison.
