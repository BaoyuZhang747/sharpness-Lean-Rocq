(** The actual left Kan extension along a fiber inclusion. Its pointwise
    values are arbitrary direct sums over base arrows; exactness and the
    adjunction follow from the proved comma universal properties. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryAdjunction
  CategoryLimits CategoryColimitMaps CategoryComma CategoryFibration CategoryFiberLanComma
  CategoryInitialFamily CategoryModules CategoryModuleLinear CategoryModuleDirectSums
  CategoryModuleDirectSumMaps CategoryModuleTerminalFamily CategoryModuleTerminalMaps
  CategoryLeftKan CategoryLeftKanAdjunction CategoryInjectives ModuleDiagrams
  ModuleInfrastructure CategoryResolutionTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section FiberLan.
Variable R : pzRingType.
Variables C D : category.
Variable p : functor C D.
Variable hp : fibration p.
Variable b : D.

Definition fiber_lan_comma_colimit (M : module_diagram R (fiber_category p b)) (a : C) :=
  terminal_family_colimit (fiber_comma_terminal_family hp b a)
    (functor_comp (costructured_projection (fiber_inclusion p b) a) M).

Definition fiber_lan : functor (functor_category (fiber_category p b) (module_category R))
    (functor_category C (module_category R)) :=
  pointwise_lan_functor (fiber_inclusion p b) fiber_lan_comma_colimit.

Definition fiber_lan_adjunction :
    adjunction fiber_lan (precomposition (module_category R) (fiber_inclusion p b)) :=
  pointwise_lan_adjunction (fiber_inclusion p b) fiber_lan_comma_colimit.

Definition fiber_lan_sum (M : module_diagram R (fiber_category p b)) (a : C) : lmodType R :=
  module_sum_type (fun alpha : hom D b (fobj p a) =>
    fobj M (lift_fiber_object (@hp a b alpha))).

Definition fiber_lan_sum_iso (M : module_diagram R (fiber_category p b)) (a : C) :
    @isomorphism (module_category R) (fobj (fobj fiber_lan M) a) (fiber_lan_sum M a) :=
  iso_refl _.

Lemma fiber_lan_map_sum {M N : module_diagram R (fiber_category p b)} (u : nat_trans M N) a :
    component (fmap fiber_lan u) a = module_hom_of_linear
      (sum_map (fun alpha : hom D b (fobj p a) =>
        module_hom_to_linear (component u (lift_fiber_object (@hp a b alpha))))).
Proof.
exact (@terminal_colimit_map_sum R (costructured_category (fiber_inclusion p b) a)
  (fiber_comma_terminal_family hp b a)
  (functor_comp (costructured_projection (fiber_inclusion p b) a) M)
  (functor_comp (costructured_projection (fiber_inclusion p b) a) N)
  (nat_whisker_left (costructured_projection (fiber_inclusion p b) a) u)).
Qed.

Definition fiber_lan_sum_functor (a : C) :
    functor (functor_category (fiber_category p b) (module_category R)) (module_category R).
Proof.
refine (@Build_functor (functor_category (fiber_category p b) (module_category R))
  (module_category R) (fun M => fiber_lan_sum M a)
  (fun M N u => module_hom_of_linear (sum_map (fun alpha : hom D b (fobj p a) =>
    module_hom_to_linear (component u (lift_fiber_object (@hp a b alpha)))))) _ _).
- intro M. rewrite -fiber_lan_map_sum.
  exact (congr1 (fun t : nat_trans (fobj fiber_lan M) (fobj fiber_lan M) => component t a)
    (fmap_id fiber_lan M)).
- intros M N O u v. rewrite -!fiber_lan_map_sum.
  exact (congr1 (fun t : nat_trans (fobj fiber_lan M) (fobj fiber_lan O) => component t a)
    (fmap_compose fiber_lan u v)).
Defined.

Lemma fiber_lan_sum_iso_natural a {M N : module_diagram R (fiber_category p b)} (u : nat_trans M N) :
    @compose (module_category R) _ _ _ (component (fmap fiber_lan u) a)
      (iso_hom (fiber_lan_sum_iso N a)) =
    @compose (module_category R) _ _ _ (iso_hom (fiber_lan_sum_iso M a))
      (fmap (fiber_lan_sum_functor a) u).
Proof.
change (@compose (module_category R) _ _ _ (component (fmap fiber_lan u) a) (identity _) =
  @compose (module_category R) _ _ _ (identity _) (fmap (fiber_lan_sum_functor a) u)).
rewrite compose_id_left compose_id_right. exact: fiber_lan_map_sum.
Qed.

Theorem fiber_lan_preserves_injections : diagram_functor_preserves_injections fiber_lan.
Proof.
intros M N u hu a. rewrite fiber_lan_map_sum.
apply sum_map_injective; intro alpha; exact: hu.
Qed.

Theorem fiber_lan_preserves_exact : diagram_functor_preserves_exact fiber_lan.
Proof.
intros M N O u v he a z. rewrite !fiber_lan_map_sum.
exact (@sum_map_exact R (hom D b (fobj p a))
  (fun alpha => fobj M (lift_fiber_object (@hp a b alpha)))
  (fun alpha => fobj N (lift_fiber_object (@hp a b alpha)))
  (fun alpha => fobj O (lift_fiber_object (@hp a b alpha)))
  (fun alpha => module_hom_to_linear (component u (lift_fiber_object (@hp a b alpha))))
  (fun alpha => module_hom_to_linear (component v (lift_fiber_object (@hp a b alpha))))
  (fun alpha => he (lift_fiber_object (@hp a b alpha))) z).
Qed.

Theorem fiber_lan_preserves_monomorphisms : preserves_monomorphisms fiber_lan.
Proof.
intros M N u hu. apply pointwise_injective_monomorphism.
apply fiber_lan_preserves_injections. exact ((proj1 (diagram_monomorphism_iff u)) hu).
Qed.

Theorem fiber_restriction_preserves_injectives (M : module_diagram R C) :
    injective_object (functor_category C (module_category R)) M ->
    injective_object (functor_category (fiber_category p b) (module_category R))
      (functor_comp (fiber_inclusion p b) M).
Proof.
exact (@right_adjoint_preserves_injectives
  (functor_category (fiber_category p b) (module_category R))
  (functor_category C (module_category R)) fiber_lan
  (precomposition (module_category R) (fiber_inclusion p b))
  fiber_lan_adjunction fiber_lan_preserves_monomorphisms M).
Qed.
End FiberLan.

Arguments fiber_lan {R C D p} hp b.
Arguments fiber_lan_adjunction {R C D p} hp b.
Arguments fiber_restriction_preserves_injectives {R C D p} hp b M.
