(** Colimits of module diagrams over a discrete terminal family are actual
    arbitrary dependent direct sums, with the universal property proved. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryLimits CategoryInitialFamily
  CategoryModules CategoryModuleLinear CategoryModuleDirectSums.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section TerminalFamily.
Variable R : pzRingType.
Variable C : category.
Variable T : initial_family (opposite C).
Variable F : module_diagram R C.

Definition terminal_family_sum : lmodType R :=
  module_sum_type (fun i => fobj F (initial_family_object T i)).

Definition terminal_family_leg_from (x : C)
    (z : {i : initial_family_index T & hom C x (initial_family_object T i)}) :
    module_hom (fobj F x) terminal_family_sum :=
  module_hom_comp (fmap F (projT2 z))
    (module_hom_of_linear (@sum_single R (initial_family_index T)
      (fun i => fobj F (initial_family_object T i)) (projT1 z))).

Definition terminal_family_leg x := terminal_family_leg_from (initial_family_choice T x).

Definition terminal_family_cocone : cocone F terminal_family_sum.
Proof.
refine (@Build_cocone C (module_category R) F terminal_family_sum terminal_family_leg _).
intros x y f.
transitivity (terminal_family_leg_from (initial_family_compose T f (initial_family_choice T y))).
- unfold terminal_family_leg. destruct (initial_family_choice T y) as [i h].
  apply module_hom_ext; intro v.
  change (@sum_single R (initial_family_index T) (fun i => fobj F (initial_family_object T i)) i
    (module_hom_fun (fmap F h) (module_hom_fun (fmap F f) v)) =
    @sum_single R (initial_family_index T) (fun i => fobj F (initial_family_object T i)) i
    (module_hom_fun (fmap F (compose f h)) v)).
  apply f_equal. exact (Logic.eq_sym (congr1 (fun g : module_hom (fobj F x)
    (fobj F (initial_family_object T i)) => g v) (fmap_compose F f h))).
- unfold terminal_family_leg. rewrite (initial_family_choice_natural T f). reflexivity.
Defined.

Lemma terminal_family_leg_self i : terminal_family_leg (initial_family_object T i) =
    module_hom_of_linear (@sum_single R (initial_family_index T)
      (fun i => fobj F (initial_family_object T i)) i).
Proof.
unfold terminal_family_leg. rewrite initial_family_choice_self.
apply module_hom_ext; intro v.
change (@sum_single R (initial_family_index T) (fun i => fobj F (initial_family_object T i)) i
  (module_hom_fun (fmap F (identity (initial_family_object T i))) v) =
  @sum_single R (initial_family_index T) (fun i => fobj F (initial_family_object T i)) i v).
rewrite fmap_id. reflexivity.
Qed.

Definition terminal_family_desc {W : lmodType R} (s : cocone F W) :
    module_hom terminal_family_sum W :=
  module_hom_of_linear (@sum_lift R (initial_family_index T)
    (fun i => fobj F (initial_family_object T i)) W
    (fun i => module_hom_to_linear (cocone_leg s (initial_family_object T i)))).

Lemma terminal_family_desc_fac {W : lmodType R} (s : cocone F W) x :
    @compose (module_category R) _ _ _ (terminal_family_leg x) (terminal_family_desc s) = cocone_leg s x.
Proof.
unfold terminal_family_leg. destruct (initial_family_choice T x) as [i h].
apply module_hom_ext; intro v.
change (@sum_lift R (initial_family_index T) (fun i => fobj F (initial_family_object T i)) W
  (fun i => module_hom_to_linear (cocone_leg s (initial_family_object T i)))
  (@sum_single R (initial_family_index T) (fun i => fobj F (initial_family_object T i)) i
    (module_hom_fun (fmap F h) v)) = module_hom_fun (cocone_leg s x) v).
rewrite sum_lift_single.
exact (congr1 (fun g : module_hom (fobj F x) W => g v) (cocone_natural s h)).
Qed.

Definition terminal_family_colimit : colimiting_cocone F.
Proof.
refine (@Build_colimiting_cocone C (module_category R) F terminal_family_sum
  terminal_family_cocone (fun W s => terminal_family_desc s) _ _).
- intros W s x; exact (terminal_family_desc_fac s x).
- intros W s g hg. apply module_hom_ext; intro v.
  apply (@sum_lift_unique R (initial_family_index T)
    (fun i => fobj F (initial_family_object T i)) W
    (fun i => module_hom_to_linear (cocone_leg s (initial_family_object T i)))
    (module_hom_to_linear g)).
  intros i w.
  have h := hg (initial_family_object T i).
  change (@compose (module_category R) _ _ _ (terminal_family_leg (initial_family_object T i)) g =
    cocone_leg s (initial_family_object T i)) in h.
  rewrite terminal_family_leg_self in h.
  exact (congr1 (fun k : module_hom (fobj F (initial_family_object T i)) W => k w) h).
Defined.
End TerminalFamily.

Arguments terminal_family_colimit {R C} T F.


