(** Uniqueness up to actual chain homotopy of projective-resolution lifts. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  ModuleDiagrams CategoryDiagramAdditive CategoryEnoughProjectives
  CategoryEnoughProjectivesResolution CategoryEnoughProjectivesComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPEnoughProjectives DPEnoughProjectiveResolutions DPProjectiveComparison.
Local Open Scope ring_scope.

Module DPProjectiveHomotopy.
Record projective_resolution_homotopy {R : pzRingType} {C : category}
    {F G : module_diagram R C} {X : projective_resolution F}
    {Y : projective_resolution G} {u : nat_trans F G}
    (f g : projective_resolution_map X Y u) := {
  projective_homotopy_at : forall n, nat_trans (projective_term X n) (projective_term Y n.+1);
  projective_homotopy_zero : forall x (v : fobj (projective_term X 0%N) x),
    module_hom_fun (component (projective_resolution_map_at f 0%N) x) v -
      module_hom_fun (component (projective_resolution_map_at g 0%N) x) v =
    module_hom_fun (component (projective_d Y 0%N) x)
      (module_hom_fun (component (projective_homotopy_at 0%N) x) v);
  projective_homotopy_succ : forall n x (v : fobj (projective_term X n.+1) x),
    module_hom_fun (component (projective_resolution_map_at f n.+1) x) v -
      module_hom_fun (component (projective_resolution_map_at g n.+1) x) v =
    module_hom_fun (component (projective_homotopy_at n) x)
      (module_hom_fun (component (projective_d X n) x) v) +
    module_hom_fun (component (projective_d Y n.+1) x)
      (module_hom_fun (component (projective_homotopy_at n.+1) x) v)
}.
Arguments projective_homotopy_at {R C F G X Y u f g} _ n.
Arguments projective_homotopy_zero {R C F G X Y u f g} _ x v.
Arguments projective_homotopy_succ {R C F G X Y u f g} _ n x v.

Section Construction.
Variables (R : pzRingType) (C : category).
Variables F G : module_diagram R C.
Variables (X : projective_resolution F) (Y : projective_resolution G).
Variable u : nat_trans F G.
Variables f g : projective_resolution_map X Y u.
Definition comparison_difference n : nat_trans (projective_term X n) (projective_term Y n) :=
  diagram_sub (projective_resolution_map_at f n) (projective_resolution_map_at g n).
Lemma comparison_difference_commutes n x (v : fobj (projective_term X n.+1) x) :
    module_hom_fun (component (projective_d Y n) x)
      (module_hom_fun (component (comparison_difference n.+1) x) v) =
    module_hom_fun (component (comparison_difference n) x)
      (module_hom_fun (component (projective_d X n) x) v).
Proof.
rewrite !diagram_sub_coordinate module_hom_sub !projective_resolution_map_commutes; reflexivity.
Qed.
Lemma comparison_difference_augmentation x (v : fobj (projective_term X 0%N) x) :
    module_hom_fun (component (projective_augmentation Y) x)
      (module_hom_fun (component (comparison_difference 0%N) x) v) = 0.
Proof.
have hf := congr1 (fun a : nat_trans (projective_term X 0%N) G =>
  module_hom_fun (component a x) v) (projective_resolution_map_augmentation f).
have hg := congr1 (fun a : nat_trans (projective_term X 0%N) G =>
  module_hom_fun (component a x) v) (projective_resolution_map_augmentation g).
rewrite diagram_sub_coordinate module_hom_sub.
transitivity (module_hom_fun (component (nat_comp (projective_augmentation X) u) x) v -
  module_hom_fun (component (nat_comp (projective_augmentation X) u) x) v).
- exact (congr2 (fun a b => a - b) hf hg).
- exact: subrr.
Qed.

Definition homotopy_state_property n
    (s : nat_trans (projective_term X n) (projective_term Y n.+1)) :=
  forall x (v : fobj (projective_term X n.+1) x),
    module_hom_fun (component (projective_d Y n) x)
      (module_hom_fun (component s x) (module_hom_fun (component (projective_d X n) x) v)) =
    module_hom_fun (component (comparison_difference n) x)
      (module_hom_fun (component (projective_d X n) x) v).
Arguments homotopy_state_property n s : clear implicits.
Definition homotopy_state n :=
  {s : nat_trans (projective_term X n) (projective_term Y n.+1) | homotopy_state_property n s}.
Lemma homotopy_zero_exists : exists s : nat_trans (projective_term X 0%N) (projective_term Y 1%N),
    nat_comp s (projective_d Y 0%N) = comparison_difference 0%N.
Proof.
apply (@projective_diagram_factor R C (projective_term Y 1%N) (projective_term Y 0%N)
  (projective_term X 0%N) (projective_d Y 0%N) (projective_terms_projective X 0%N)).
intros x v; apply (proj1 (@projective_exact_augmentation R C G Y x _)).
exact: comparison_difference_augmentation.
Qed.
Definition homotopy_zero_map := proj1_sig (constructive_indefinite_description homotopy_zero_exists).
Lemma homotopy_zero_factor : nat_comp homotopy_zero_map (projective_d Y 0%N) = comparison_difference 0%N.
Proof. exact (proj2_sig (constructive_indefinite_description homotopy_zero_exists)). Qed.
Lemma homotopy_zero_property : homotopy_state_property 0%N homotopy_zero_map.
Proof.
intros x v; exact (congr1 (fun a : nat_trans (projective_term X 0%N) (projective_term Y 0%N) =>
  module_hom_fun (component a x) (module_hom_fun (component (projective_d X 0%N) x) v)) homotopy_zero_factor).
Qed.
Definition homotopy_initial_state : homotopy_state 0%N := exist _ homotopy_zero_map homotopy_zero_property.
Definition homotopy_residual n (s : homotopy_state n) :
    nat_trans (projective_term X n.+1) (projective_term Y n.+1) :=
  diagram_sub (comparison_difference n.+1) (nat_comp (projective_d X n) (proj1_sig s)).
Lemma homotopy_residual_cycle n (s : homotopy_state n) x (v : fobj (projective_term X n.+1) x) :
    module_hom_fun (component (projective_d Y n) x)
      (module_hom_fun (component (homotopy_residual s) x) v) = 0.
Proof.
change (module_hom_fun (component (projective_d Y n) x)
  (module_hom_fun (component (comparison_difference n.+1) x) v -
    module_hom_fun (component (proj1_sig s) x) (module_hom_fun (component (projective_d X n) x) v)) = 0).
rewrite module_hom_sub comparison_difference_commutes (proj2_sig s x v); exact: subrr.
Qed.
Lemma homotopy_next_exists n (s : homotopy_state n) :
    exists t : nat_trans (projective_term X n.+1) (projective_term Y n.+2),
      nat_comp t (projective_d Y n.+1) = homotopy_residual s /\ homotopy_state_property n.+1 t.
Proof.
have hm : forall x (v : fobj (projective_term X n.+1) x), exists w,
    module_hom_fun (component (projective_d Y n.+1) x) w =
      module_hom_fun (component (homotopy_residual s) x) v.
  intros x v; apply (proj1 (@projective_exact_successor R C G Y n x _)).
  exact: homotopy_residual_cycle.
have [t ht] := @projective_diagram_factor R C (projective_term Y n.+2)
  (projective_term Y n.+1) (projective_term X n.+1) (projective_d Y n.+1)
  (projective_terms_projective X n.+1) (homotopy_residual s) hm.
exists t; split; first exact ht.
intros x v.
have h := congr1 (fun a : nat_trans (projective_term X n.+1) (projective_term Y n.+1) =>
  module_hom_fun (component a x) (module_hom_fun (component (projective_d X n.+1) x) v)) ht.
transitivity (module_hom_fun (component (homotopy_residual s) x)
  (module_hom_fun (component (projective_d X n.+1) x) v)); first exact h.
change (module_hom_fun (component (comparison_difference n.+1) x)
  (module_hom_fun (component (projective_d X n.+1) x) v) -
  module_hom_fun (component (proj1_sig s) x)
    (module_hom_fun (component (projective_d X n) x)
      (module_hom_fun (component (projective_d X n.+1) x) v)) =
  module_hom_fun (component (comparison_difference n.+1) x)
    (module_hom_fun (component (projective_d X n.+1) x) v)).
rewrite projective_d_squared module_hom_zero subr0; reflexivity.
Qed.
Definition homotopy_next n (s : homotopy_state n) : homotopy_state n.+1 :=
  exist _ (proj1_sig (constructive_indefinite_description (homotopy_next_exists s)))
    (proj2 (proj2_sig (constructive_indefinite_description (homotopy_next_exists s)))).
Lemma homotopy_next_factor n (s : homotopy_state n) :
    nat_comp (proj1_sig (homotopy_next s)) (projective_d Y n.+1) = homotopy_residual s.
Proof. exact (proj1 (proj2_sig (constructive_indefinite_description (homotopy_next_exists s)))). Qed.
Fixpoint homotopy_sequence n : homotopy_state n :=
  match n as k return homotopy_state k with
  | 0%N => homotopy_initial_state
  | k.+1 => homotopy_next (homotopy_sequence k)
  end.
Definition projective_resolution_maps_homotopic : projective_resolution_homotopy f g.
Proof.
refine (@Build_projective_resolution_homotopy R C F G X Y u f g
  (fun n => proj1_sig (homotopy_sequence n)) _ _).
- intros x v; symmetry.
  exact (congr1 (fun a : nat_trans (projective_term X 0%N) (projective_term Y 0%N) =>
    module_hom_fun (component a x) v) homotopy_zero_factor).
- intros n x v.
  have h := congr1 (fun a : nat_trans (projective_term X n.+1) (projective_term Y n.+1) =>
    module_hom_fun (component a x) v) (homotopy_next_factor (homotopy_sequence n)).
  change (module_hom_fun (component (projective_d Y n.+1) x)
    (module_hom_fun (component (proj1_sig (homotopy_sequence n.+1)) x) v) =
    module_hom_fun (component (comparison_difference n.+1) x) v -
    module_hom_fun (component (proj1_sig (homotopy_sequence n)) x)
      (module_hom_fun (component (projective_d X n) x) v)) in h.
  rewrite h; symmetry; rewrite addrC; exact: subrK.
Defined.
End Construction.
Arguments projective_resolution_maps_homotopic {R C F G X Y u} f g.

Definition projective_resolution_identity {R : pzRingType} {C : category}
    {F : module_diagram R C} (X : projective_resolution F) : projective_resolution_map X X (nat_id F).
Proof.
refine (@Build_projective_resolution_map R C F F X X (nat_id F)
  (fun n => nat_id (projective_term X n)) _ _).
- intros n x v; reflexivity.
- apply nat_trans_ext=> x; apply module_hom_ext=> v; reflexivity.
Defined.
Definition projective_resolution_composition {R : pzRingType} {C : category}
    {F G H : module_diagram R C} {X : projective_resolution F}
    {Y : projective_resolution G} {Z : projective_resolution H}
    {u : nat_trans F G} {v : nat_trans G H}
    (f : projective_resolution_map X Y u) (g : projective_resolution_map Y Z v) :
    projective_resolution_map X Z (nat_comp u v).
Proof.
refine (@Build_projective_resolution_map R C F H X Z (nat_comp u v)
  (fun n => nat_comp (projective_resolution_map_at f n) (projective_resolution_map_at g n)) _ _).
- intros n x w.
  change (module_hom_fun (component (projective_d Z n) x)
    (module_hom_fun (component (projective_resolution_map_at g n.+1) x)
      (module_hom_fun (component (projective_resolution_map_at f n.+1) x) w)) =
    module_hom_fun (component (projective_resolution_map_at g n) x)
      (module_hom_fun (component (projective_resolution_map_at f n) x)
        (module_hom_fun (component (projective_d X n) x) w))).
  by rewrite !projective_resolution_map_commutes.
- apply nat_trans_ext=> x; apply module_hom_ext=> w.
  have hf := congr1 (fun a : nat_trans (projective_term X 0%N) G =>
    module_hom_fun (component a x) w) (projective_resolution_map_augmentation f).
  have hg := congr1 (fun a : nat_trans (projective_term Y 0%N) H =>
    module_hom_fun (component a x) (module_hom_fun (component (projective_resolution_map_at f 0%N) x) w))
    (projective_resolution_map_augmentation g).
  transitivity (module_hom_fun (component v x)
    (module_hom_fun (component (projective_augmentation Y) x)
      (module_hom_fun (component (projective_resolution_map_at f 0%N) x) w))).
  + exact hg.
  + exact (congr1 (module_hom_fun (component v x)) hf).
Defined.
End DPProjectiveHomotopy.
