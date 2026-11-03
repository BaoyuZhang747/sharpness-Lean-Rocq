(** Actual comparison maps between augmented injective resolutions.
    Maps are extended through the image of each differential; injectivity
    and augmented exactness supply every extension. *)
From mathcomp Require Import all_ssreflect ssralg boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryInjectives ModuleDiagrams HomologicalDiagramInjectives
  CategoryInjectiveResolution CategoryDiagramImage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Record diagram_cochain_map {R : pzRingType} {C : category}
    (K L : @diagram_complex R C) := {
  diagram_cochain_map_at : forall n, nat_trans (diagram_term K n) (diagram_term L n);
  diagram_cochain_map_commutes : forall n x (v : fobj (diagram_term K n) x),
    module_hom_fun (component (diagram_d L n) x)
      (module_hom_fun (component (diagram_cochain_map_at n) x) v) =
    module_hom_fun (component (diagram_cochain_map_at n.+1) x)
      (module_hom_fun (component (diagram_d K n) x) v)
}.

Arguments diagram_cochain_map_at {R C K L} _ n.
Arguments diagram_cochain_map_commutes {R C K L} _ n x v.

Record injective_resolution_map {R : pzRingType} {C : category}
    {F G : module_diagram R C} (X : injective_resolution F)
    (Y : injective_resolution G) (u : nat_trans F G) := {
  resolution_map_complex : diagram_cochain_map
    (injective_resolution_complex X) (injective_resolution_complex Y);
  resolution_map_augmentation :
    nat_comp (injective_resolution_augmentation X)
      (diagram_cochain_map_at resolution_map_complex 0%N) =
    nat_comp u (injective_resolution_augmentation Y)
}.

Arguments resolution_map_complex {R C F G X Y u} _.
Arguments resolution_map_augmentation {R C F G X Y u} _.

Section ComparisonConstruction.
Variable R : pzRingType.
Variable C : category.
Variables F G : module_diagram R C.
Variable X : injective_resolution F.
Variable Y : injective_resolution G.
Variable u : nat_trans F G.
Let K := injective_resolution_complex X.
Let L := injective_resolution_complex Y.

Definition comparison_cycle_property n (f : nat_trans (diagram_term K n) (diagram_term L n)) :=
  forall x (v : fobj (diagram_term K n) x),
    module_hom_fun (component (diagram_d K n) x) v = 0 ->
    module_hom_fun (component (diagram_d L n) x) (module_hom_fun (component f x) v) = 0.

Arguments comparison_cycle_property n f : clear implicits.

Lemma comparison_zero_exists :
    exists f : nat_trans (diagram_term K 0%N) (diagram_term L 0%N),
      nat_comp (injective_resolution_augmentation X) f =
        nat_comp u (injective_resolution_augmentation Y).
Proof.
  apply (injective_resolution_term_injective Y 0%N).
  apply pointwise_injective_monomorphism.
  apply injective_resolution_augmentation_injective.
Qed.

Definition comparison_zero_map :=
  proj1_sig (constructive_indefinite_description comparison_zero_exists).

Lemma comparison_zero_augmentation :
    nat_comp (injective_resolution_augmentation X) comparison_zero_map =
      nat_comp u (injective_resolution_augmentation Y).
Proof. exact (proj2_sig (constructive_indefinite_description comparison_zero_exists)). Qed.

Lemma comparison_zero_cycles : comparison_cycle_property 0%N comparison_zero_map.
Proof.
  intros x v hv.
  destruct ((proj1 (injective_resolution_exact_zero X x v)) hv) as [w <-].
  pose proof (f_equal (fun a : nat_trans F (diagram_term L 0%N) =>
    module_hom_fun (component a x) w) comparison_zero_augmentation) as h.
  transitivity (module_hom_fun (component (diagram_d L 0%N) x)
    (module_hom_fun (component (injective_resolution_augmentation Y) x)
      (module_hom_fun (component u x) w))).
  - apply f_equal. exact h.
  - exact (injective_resolution_augmentation_zero Y x _).
Qed.

Definition comparison_state n :=
  {f : nat_trans (diagram_term K n) (diagram_term L n) | comparison_cycle_property n f}.

Definition comparison_initial_state : comparison_state 0%N :=
  exist _ comparison_zero_map comparison_zero_cycles.

Lemma comparison_next_exists n (s : comparison_state n) :
    exists f : nat_trans (diagram_term K n.+1) (diagram_term L n.+1),
      nat_comp (diagram_d K n) f = nat_comp (proj1_sig s) (diagram_d L n) /\
      comparison_cycle_property n.+1 f.
Proof.
  destruct (@injective_diagram_factor R C (diagram_term K n) (diagram_term K n.+1)
    (diagram_d K n) (diagram_term L n.+1)
    (injective_resolution_term_injective Y n.+1)
    (nat_comp (proj1_sig s) (diagram_d L n)) (proj2_sig s)) as [f hf].
  exists f. split; first exact hf.
  intros x v hv.
  destruct (injective_resolution_exact_successor X n x v hv) as [w <-].
  pose proof (f_equal (fun a : nat_trans (diagram_term K n) (diagram_term L n.+1) =>
    module_hom_fun (component a x) w) hf) as h.
  transitivity (module_hom_fun (component (diagram_d L n.+1) x)
    (module_hom_fun (component (diagram_d L n) x)
      (module_hom_fun (component (proj1_sig s) x) w))).
  - apply f_equal. exact h.
  - exact (@diagram_d2 R C L n x _).
Qed.

Definition comparison_next n (s : comparison_state n) : comparison_state n.+1 :=
  exist _ (proj1_sig (constructive_indefinite_description (comparison_next_exists s)))
    (proj2 (proj2_sig (constructive_indefinite_description (comparison_next_exists s)))).

Lemma comparison_next_factor n (s : comparison_state n) :
    nat_comp (diagram_d K n) (proj1_sig (comparison_next s)) =
      nat_comp (proj1_sig s) (diagram_d L n).
Proof. exact (proj1 (proj2_sig (constructive_indefinite_description (comparison_next_exists s)))). Qed.

Fixpoint comparison_sequence (n : nat) : comparison_state n :=
  match n as k return comparison_state k with
  | 0%N => comparison_initial_state
  | k.+1 => comparison_next (comparison_sequence k)
  end.

Definition constructed_resolution_cochain_map : diagram_cochain_map K L.
Proof.
  refine (@Build_diagram_cochain_map R C K L
    (fun n => proj1_sig (comparison_sequence n)) _).
  intros n x v. symmetry.
  exact (f_equal (fun a : nat_trans (diagram_term K n) (diagram_term L n.+1) =>
    module_hom_fun (component a x) v) (comparison_next_factor (comparison_sequence n))).
Defined.

Definition injective_resolution_comparison : injective_resolution_map X Y u :=
  @Build_injective_resolution_map R C F G X Y u constructed_resolution_cochain_map
    comparison_zero_augmentation.
End ComparisonConstruction.

Arguments injective_resolution_comparison {R C F G} X Y u.
