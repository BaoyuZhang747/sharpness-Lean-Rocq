(** Restriction to an actual structured comma preserves injectives.
    The left adjoint is constructed from a discrete terminal family and its
    exactness follows from arbitrary direct sums. No fibration is assumed. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryAdjunction
  CategoryLimits CategoryColimitMaps CategoryComma CategoryStructured
  CategoryInitialFamily CategoryModules CategoryModuleLinear
  CategoryModuleDirectSums CategoryModuleDirectSumMaps CategoryModuleTerminalFamily
  CategoryModuleTerminalMaps CategoryLeftKan CategoryLeftKanAdjunction
  CategoryInjectives ModuleDiagrams ModuleInfrastructure CategoryResolutionTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CommaTerminalFamily.
Variables C D : category.
Variable r : functor C D.
Variable d : D.
Variable c : C.

Definition ran_comma_lan_label
    (X : costructured_category (structured_projection r d) c) :
    hom D d (fobj r c) :=
  compose (structured_arrow (costructured_source X))
    (fmap r (costructured_arrow X)).

Definition ran_comma_lan_terminal (a : hom D d (fobj r c)) :
    costructured_category (structured_projection r d) c :=
  @Build_costructured_object (structured_category r d) C
    (structured_projection r d) c (structured_point r c a) (identity c).

Lemma ran_comma_lan_terminal_label a :
    ran_comma_lan_label (ran_comma_lan_terminal a) = a.
Proof. unfold ran_comma_lan_label, ran_comma_lan_terminal; simpl.
by rewrite fmap_id compose_id_right.
Qed.

Lemma ran_comma_lan_label_map
    {X Y : costructured_category (structured_projection r d) c}
    (f : hom (costructured_category (structured_projection r d) c) X Y) :
    ran_comma_lan_label X = ran_comma_lan_label Y.
Proof.
unfold ran_comma_lan_label.
rewrite -(costructured_commutes f) fmap_compose -compose_assoc.
change (compose
  (compose (structured_arrow (costructured_source X))
    (fmap r (structured_map (costructured_map f))))
  (fmap r (costructured_arrow Y)) =
  compose (structured_arrow (costructured_source Y))
    (fmap r (costructured_arrow Y))).
by rewrite structured_commutes.
Qed.

Definition ran_comma_lan_factor
    (X : costructured_category (structured_projection r d) c) :
    hom (costructured_category (structured_projection r d) c) X
      (ran_comma_lan_terminal (ran_comma_lan_label X)).
Proof.
refine (@Build_costructured_hom (structured_category r d) C
  (structured_projection r d) c X
  (ran_comma_lan_terminal (ran_comma_lan_label X))
  (@structured_morphism C D r d (costructured_source X)
    (structured_point r c (ran_comma_lan_label X))
    (costructured_arrow X) (Logic.eq_refl _)) _).
change (compose (costructured_arrow X) (identity c) = costructured_arrow X).
exact: compose_id_right.
Defined.

Lemma ran_comma_lan_factor_unique
    (X : costructured_category (structured_projection r d) c) a
    (f g : hom (costructured_category (structured_projection r d) c) X
      (ran_comma_lan_terminal a)) : f = g.
Proof.
apply costructured_hom_ext; apply costructured_hom_ext.
have hf := costructured_commutes f.
have hg := costructured_commutes g.
change (compose (structured_map (costructured_map f)) (identity c) =
  costructured_arrow X) in hf.
change (compose (structured_map (costructured_map g)) (identity c) =
  costructured_arrow X) in hg.
rewrite compose_id_right in hf.
rewrite compose_id_right in hg.
exact (Logic.eq_trans hf (Logic.eq_sym hg)).
Qed.

Definition ran_comma_lan_terminal_family :
    initial_family (opposite (costructured_category (structured_projection r d) c)).
Proof.
refine (@Build_initial_family
  (opposite (costructured_category (structured_projection r d) c))
  (hom D d (fobj r c)) ran_comma_lan_terminal
  (fun X => existT _ (ran_comma_lan_label X) (ran_comma_lan_factor X)) _).
intros X [a f].
have h : a = ran_comma_lan_label X.
  by rewrite (ran_comma_lan_label_map f) ran_comma_lan_terminal_label.
apply eq_sigT_uncurried; exists h; apply ran_comma_lan_factor_unique.
Defined.
End CommaTerminalFamily.

Arguments ran_comma_lan_terminal_family {C D} r d c.

Section CommaRestriction.
Variable R : pzRingType.
Variables C D : category.
Variable r : functor C D.
Variable d : D.

Definition ran_comma_lan_colimit
    (M : module_diagram R (structured_category r d)) (c : C) :=
  terminal_family_colimit (ran_comma_lan_terminal_family r d c)
    (functor_comp (costructured_projection (structured_projection r d) c) M).

Definition ran_comma_lan :
    functor (functor_category (structured_category r d) (module_category R))
      (functor_category C (module_category R)) :=
  pointwise_lan_functor (structured_projection r d) ran_comma_lan_colimit.

Definition ran_comma_lan_adjunction : adjunction ran_comma_lan
    (precomposition (module_category R) (structured_projection r d)) :=
  pointwise_lan_adjunction (structured_projection r d) ran_comma_lan_colimit.

Lemma ran_comma_lan_map_sum
    {M N : module_diagram R (structured_category r d)} (u : nat_trans M N) c :
    component (fmap ran_comma_lan u) c =
      module_hom_of_linear (sum_map (fun a : hom D d (fobj r c) =>
        module_hom_to_linear (component u (structured_point r c a)))).
Proof.
exact (@terminal_colimit_map_sum R
  (costructured_category (structured_projection r d) c)
  (ran_comma_lan_terminal_family r d c)
  (functor_comp (costructured_projection (structured_projection r d) c) M)
  (functor_comp (costructured_projection (structured_projection r d) c) N)
  (nat_whisker_left (costructured_projection (structured_projection r d) c) u)).
Qed.

Theorem ran_comma_lan_preserves_injections :
    diagram_functor_preserves_injections ran_comma_lan.
Proof.
intros M N u hu c; rewrite ran_comma_lan_map_sum.
apply sum_map_injective; intro a; exact: hu.
Qed.

Theorem ran_comma_lan_preserves_exact :
    diagram_functor_preserves_exact ran_comma_lan.
Proof.
intros M N O u v he c z; rewrite !ran_comma_lan_map_sum.
exact (@sum_map_exact R (hom D d (fobj r c))
  (fun a => fobj M (structured_point r c a))
  (fun a => fobj N (structured_point r c a))
  (fun a => fobj O (structured_point r c a))
  (fun a => module_hom_to_linear (component u (structured_point r c a)))
  (fun a => module_hom_to_linear (component v (structured_point r c a)))
  (fun a => he (structured_point r c a)) z).
Qed.

Theorem ran_comma_lan_preserves_monomorphisms : preserves_monomorphisms ran_comma_lan.
Proof.
intros M N u hu; apply pointwise_injective_monomorphism.
apply ran_comma_lan_preserves_injections.
exact ((proj1 (diagram_monomorphism_iff u)) hu).
Qed.

Theorem ran_comma_restriction_preserves_injectives (M : module_diagram R C) :
    injective_object (functor_category C (module_category R)) M ->
    injective_object
      (functor_category (structured_category r d) (module_category R))
      (functor_comp (structured_projection r d) M).
Proof.
exact (@right_adjoint_preserves_injectives
  (functor_category (structured_category r d) (module_category R))
  (functor_category C (module_category R)) ran_comma_lan
  (precomposition (module_category R) (structured_projection r d))
  ran_comma_lan_adjunction ran_comma_lan_preserves_monomorphisms M).
Qed.
End CommaRestriction.

Arguments ran_comma_restriction_preserves_injectives R {C D} r d M.
