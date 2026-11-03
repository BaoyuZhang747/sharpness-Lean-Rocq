(** The actual colimit coefficient map is the direct sum of its maps at
    the terminal family. This proves its exactness and natural formula. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryLimits CategoryColimitMaps CategoryInitialFamily
  CategoryModules CategoryModuleLinear CategoryModuleDirectSums CategoryModuleDirectSumMaps
  CategoryModuleTerminalFamily ModuleInfrastructure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Maps.
Variable R : pzRingType.
Variable C : category.
Variable T : initial_family (opposite C).
Variables F G : module_diagram R C.
Variable a : nat_trans F G.

Lemma terminal_colimit_map_single i (v : fobj F (initial_family_object T i)) :
    module_hom_fun (colimit_map (terminal_family_colimit T F) (terminal_family_colimit T G) a)
      (@sum_single R (initial_family_index T) (fun j => fobj F (initial_family_object T j)) i v) =
      @sum_single R (initial_family_index T) (fun j => fobj G (initial_family_object T j)) i
        (module_hom_fun (component a (initial_family_object T i)) v).
Proof.
have h := colimit_map_fac (terminal_family_colimit T F) (terminal_family_colimit T G) a
  (initial_family_object T i).
change (@compose (module_category R) _ _ _ (terminal_family_leg T F (initial_family_object T i))
  (colimit_map (terminal_family_colimit T F) (terminal_family_colimit T G) a) =
  @compose (module_category R) _ _ _ (component a (initial_family_object T i))
    (terminal_family_leg T G (initial_family_object T i))) in h.
rewrite !terminal_family_leg_self in h.
exact (congr1 (fun f : module_hom (fobj F (initial_family_object T i)) (terminal_family_sum T G) => f v) h).
Qed.

Lemma terminal_colimit_map_sum :
    colimit_map (terminal_family_colimit T F) (terminal_family_colimit T G) a =
      module_hom_of_linear (sum_map (fun i => module_hom_to_linear (component a (initial_family_object T i)))).
Proof.
apply module_hom_ext; intro v.
pose (f := fun i => module_hom_to_linear (module_hom_comp
  (component a (initial_family_object T i))
  (module_hom_of_linear (@sum_single R (initial_family_index T)
    (fun j => fobj G (initial_family_object T j)) i)))).
transitivity (@sum_lift R (initial_family_index T) (fun i => fobj F (initial_family_object T i))
  (terminal_family_sum T G) f v).
- apply (@sum_lift_unique R _ _ _ f (module_hom_to_linear
    (colimit_map (terminal_family_colimit T F) (terminal_family_colimit T G) a))).
  intros i w; exact: terminal_colimit_map_single.
- symmetry; apply (@sum_lift_unique R _ _ _ f
    (sum_map (fun i => module_hom_to_linear (component a (initial_family_object T i))))).
  intros i w; exact: sum_map_single.
Qed.
End Maps.

Theorem terminal_colimit_preserves_injections {R : pzRingType} {C : category}
    (T : initial_family (opposite C)) {F G : module_diagram R C} (a : nat_trans F G)
    (ha : forall x, injective (module_hom_fun (component a x))) :
    injective (module_hom_fun (colimit_map (terminal_family_colimit T F) (terminal_family_colimit T G) a)).
Proof. rewrite terminal_colimit_map_sum; apply sum_map_injective; intro i; exact: ha. Qed.

Theorem terminal_colimit_preserves_exact {R : pzRingType} {C : category}
    (T : initial_family (opposite C)) {F G H : module_diagram R C}
    (a : nat_trans F G) (b : nat_trans G H)
    (he : forall x, linear_exact (module_hom_to_linear (component a x)) (module_hom_to_linear (component b x))) :
    linear_exact
      (module_hom_to_linear (colimit_map (terminal_family_colimit T F) (terminal_family_colimit T G) a))
      (module_hom_to_linear (colimit_map (terminal_family_colimit T G) (terminal_family_colimit T H) b)).
Proof. rewrite !terminal_colimit_map_sum; apply sum_map_exact; intro i; exact: he. Qed.


