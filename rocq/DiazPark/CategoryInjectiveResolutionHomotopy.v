(** Any two comparison maps covering the same coefficient map are
    homotopic through actual natural linear maps. *)
From mathcomp Require Import all_ssreflect ssralg boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryInjectives CategoryDiagramImage CategoryDiagramAdditive
  HomologicalDiagramInjectives CategoryInjectiveResolution
  CategoryInjectiveResolutionComparison.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Record diagram_cochain_homotopy {R : pzRingType} {C : category}
    {K L : @diagram_complex R C} (f g : diagram_cochain_map K L) := {
  diagram_homotopy_at : forall n, nat_trans (diagram_term K n.+1) (diagram_term L n);
  diagram_homotopy_zero : forall x (v : fobj (diagram_term K 0%N) x),
    module_hom_fun (component (diagram_cochain_map_at f 0%N) x) v -
      module_hom_fun (component (diagram_cochain_map_at g 0%N) x) v =
    module_hom_fun (component (diagram_homotopy_at 0%N) x)
      (module_hom_fun (component (diagram_d K 0%N) x) v);
  diagram_homotopy_succ : forall n x (v : fobj (diagram_term K n.+1) x),
    module_hom_fun (component (diagram_cochain_map_at f n.+1) x) v -
      module_hom_fun (component (diagram_cochain_map_at g n.+1) x) v =
    module_hom_fun (component (diagram_d L n) x)
      (module_hom_fun (component (diagram_homotopy_at n) x) v) +
    module_hom_fun (component (diagram_homotopy_at n.+1) x)
      (module_hom_fun (component (diagram_d K n.+1) x) v)
}.

Arguments diagram_homotopy_at {R C K L f g} _ n.
Arguments diagram_homotopy_zero {R C K L f g} _ x v.
Arguments diagram_homotopy_succ {R C K L f g} _ n x v.

Section HomotopyConstruction.
Variable R : pzRingType.
Variable C : category.
Variables F G : module_diagram R C.
Variables (X : injective_resolution F) (Y : injective_resolution G).
Variable u : nat_trans F G.
Variables a b : injective_resolution_map X Y u.
Let K := injective_resolution_complex X.
Let L := injective_resolution_complex Y.
Let f := resolution_map_complex a.
Let g := resolution_map_complex b.

Definition comparison_difference n : nat_trans (diagram_term K n) (diagram_term L n) :=
  diagram_sub (diagram_cochain_map_at f n) (diagram_cochain_map_at g n).

Lemma comparison_difference_commutes n x (v : fobj (diagram_term K n) x) :
    module_hom_fun (component (diagram_d L n) x)
      (module_hom_fun (component (comparison_difference n) x) v) =
    module_hom_fun (component (comparison_difference n.+1) x)
      (module_hom_fun (component (diagram_d K n) x) v).
Proof.
  rewrite !diagram_sub_coordinate module_hom_sub.
  rewrite !diagram_cochain_map_commutes. reflexivity.
Qed.

Lemma comparison_difference_augmentation x (v : fobj F x) :
    module_hom_fun (component (comparison_difference 0%N) x)
      (module_hom_fun (component (injective_resolution_augmentation X) x) v) = 0.
Proof.
  pose proof (f_equal (fun t : nat_trans F (diagram_term L 0%N) =>
    module_hom_fun (component t x) v) (resolution_map_augmentation a)) as ha.
  pose proof (f_equal (fun t : nat_trans F (diagram_term L 0%N) =>
    module_hom_fun (component t x) v) (resolution_map_augmentation b)) as hb.
  change (module_hom_fun (component (diagram_cochain_map_at f 0%N) x)
      (module_hom_fun (component (injective_resolution_augmentation X) x) v) -
    module_hom_fun (component (diagram_cochain_map_at g 0%N) x)
      (module_hom_fun (component (injective_resolution_augmentation X) x) v) = 0).
  transitivity (module_hom_fun (component (nat_comp u (injective_resolution_augmentation Y)) x) v -
    module_hom_fun (component (nat_comp u (injective_resolution_augmentation Y)) x) v).
  - exact (f_equal2 (fun p q => p - q) ha hb).
  - apply subrr.
Qed.

Definition homotopy_state_property n
    (s : nat_trans (diagram_term K n.+1) (diagram_term L n)) :=
  forall x (v : fobj (diagram_term K n) x),
    module_hom_fun (component (diagram_d L n) x)
      (module_hom_fun (component (comparison_difference n) x) v) =
    module_hom_fun (component (diagram_d L n) x)
      (module_hom_fun (component s x)
        (module_hom_fun (component (diagram_d K n) x) v)).

Arguments homotopy_state_property n s : clear implicits.

Definition homotopy_state n :=
  {s : nat_trans (diagram_term K n.+1) (diagram_term L n) | homotopy_state_property n s}.

Lemma homotopy_zero_exists :
  exists s : nat_trans (diagram_term K 1%N) (diagram_term L 0%N),
    nat_comp (diagram_d K 0%N) s = comparison_difference 0%N.
Proof.
  apply (@injective_diagram_factor R C (diagram_term K 0%N) (diagram_term K 1%N)
    (diagram_d K 0%N) (diagram_term L 0%N) (injective_resolution_term_injective Y 0%N)).
  intros x v hv. destruct ((proj1 (injective_resolution_exact_zero X x v)) hv) as [w <-].
  exact (@comparison_difference_augmentation x w).
Qed.

Definition homotopy_zero_map :=
  proj1_sig (constructive_indefinite_description homotopy_zero_exists).

Lemma homotopy_zero_factor :
  nat_comp (diagram_d K 0%N) homotopy_zero_map = comparison_difference 0%N.
Proof. exact (proj2_sig (constructive_indefinite_description homotopy_zero_exists)). Qed.

Lemma homotopy_zero_property : homotopy_state_property 0%N homotopy_zero_map.
Proof.
  intros x v. apply f_equal. symmetry.
  exact (f_equal (fun t : nat_trans (diagram_term K 0%N) (diagram_term L 0%N) =>
    module_hom_fun (component t x) v) homotopy_zero_factor).
Qed.

Definition homotopy_initial_state : homotopy_state 0%N :=
  exist _ homotopy_zero_map homotopy_zero_property.

Definition homotopy_residual n (s : homotopy_state n) :
    nat_trans (diagram_term K n.+1) (diagram_term L n.+1) :=
  diagram_sub (comparison_difference n.+1) (nat_comp (proj1_sig s) (diagram_d L n)).

Lemma homotopy_residual_kernel n (s : homotopy_state n) x
    (v : fobj (diagram_term K n.+1) x) :
    module_hom_fun (component (diagram_d K n.+1) x) v = 0 ->
    module_hom_fun (component (homotopy_residual s) x) v = 0.
Proof.
  intro hv. destruct (injective_resolution_exact_successor X n x v hv) as [w <-].
  change (module_hom_fun (component (comparison_difference n.+1) x)
      (module_hom_fun (component (diagram_d K n) x) w) -
    module_hom_fun (component (diagram_d L n) x)
      (module_hom_fun (component (proj1_sig s) x)
        (module_hom_fun (component (diagram_d K n) x) w)) = 0).
  rewrite -comparison_difference_commutes (proj2_sig s x w). apply subrr.
Qed.

Lemma homotopy_next_exists n (s : homotopy_state n) :
    exists t : nat_trans (diagram_term K n.+2) (diagram_term L n.+1),
      nat_comp (diagram_d K n.+1) t = homotopy_residual s /\
      homotopy_state_property n.+1 t.
Proof.
  destruct (@injective_diagram_factor R C (diagram_term K n.+1) (diagram_term K n.+2)
    (diagram_d K n.+1) (diagram_term L n.+1) (injective_resolution_term_injective Y n.+1)
    (homotopy_residual s) (homotopy_residual_kernel s)) as [t ht].
  exists t. split; first exact ht.
  intros x v.
  pose proof (f_equal (fun k : nat_trans (diagram_term K n.+1) (diagram_term L n.+1) =>
    module_hom_fun (component k x) v) ht) as h.
  transitivity (module_hom_fun (component (diagram_d L n.+1) x)
    (module_hom_fun (component (homotopy_residual s) x) v)).
  - change (module_hom_fun (component (diagram_d L n.+1) x)
      (module_hom_fun (component (comparison_difference n.+1) x) v) =
    module_hom_fun (component (diagram_d L n.+1) x)
      (module_hom_fun (component (comparison_difference n.+1) x) v -
       module_hom_fun (component (diagram_d L n) x)
        (module_hom_fun (component (proj1_sig s) x) v))).
    rewrite module_hom_sub (@diagram_d2 R C L n x _) subr0. reflexivity.
  - apply f_equal. symmetry. exact h.
Qed.

Definition homotopy_next n (s : homotopy_state n) : homotopy_state n.+1 :=
  exist _ (proj1_sig (constructive_indefinite_description (homotopy_next_exists s)))
    (proj2 (proj2_sig (constructive_indefinite_description (homotopy_next_exists s)))).

Lemma homotopy_next_factor n (s : homotopy_state n) :
    nat_comp (diagram_d K n.+1) (proj1_sig (homotopy_next s)) = homotopy_residual s.
Proof. exact (proj1 (proj2_sig (constructive_indefinite_description (homotopy_next_exists s)))). Qed.

Fixpoint homotopy_sequence n : homotopy_state n :=
  match n as k return homotopy_state k with
  | 0%N => homotopy_initial_state
  | k.+1 => homotopy_next (homotopy_sequence k)
  end.

Definition injective_resolution_maps_homotopic : diagram_cochain_homotopy f g.
Proof.
  refine (@Build_diagram_cochain_homotopy R C K L f g
    (fun n => proj1_sig (homotopy_sequence n)) _ _).
  - intros x v. symmetry.
    exact (f_equal (fun t : nat_trans (diagram_term K 0%N) (diagram_term L 0%N) =>
      module_hom_fun (component t x) v) homotopy_zero_factor).
  - intros n x v.
    pose proof (f_equal (fun t : nat_trans (diagram_term K n.+1) (diagram_term L n.+1) =>
      module_hom_fun (component t x) v) (homotopy_next_factor (homotopy_sequence n))) as h.
    change (module_hom_fun (component (comparison_difference n.+1) x) v =
      module_hom_fun (component (diagram_d L n) x)
        (module_hom_fun (component (proj1_sig (homotopy_sequence n)) x) v) +
      module_hom_fun (component (proj1_sig (homotopy_sequence n.+1)) x)
        (module_hom_fun (component (diagram_d K n.+1) x) v)).
    change (module_hom_fun (component (proj1_sig (homotopy_sequence n.+1)) x)
      (module_hom_fun (component (diagram_d K n.+1) x) v) =
      module_hom_fun (component (comparison_difference n.+1) x) v -
      module_hom_fun (component (diagram_d L n) x)
        (module_hom_fun (component (proj1_sig (homotopy_sequence n)) x) v)) in h.
    rewrite h addrC subrK. reflexivity.
Defined.
End HomotopyConstruction.

Arguments injective_resolution_maps_homotopic {R C F G X Y u} a b.
