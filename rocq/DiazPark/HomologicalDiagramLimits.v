(** The actual limit functor sends a natural contraction to a contraction.
    Consequently an exact nonnegative complex of injective module diagrams
    has an acyclic limit complex, including in degree zero. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryLimits CategoryLimitMaps CategoryModuleLimits CategoryModuleLimitFunctor
  CategoryInjectives ModuleDiagrams HomologicalComplex HomologicalCohomology
  HomologicalDiagramInjectives.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology.
Local Open Scope ring_scope.

Section LimitComplex.
Variable R : pzRingType.
Variable C : category.

Definition limit_action {F G : module_diagram R C} (t : nat_trans F G) :
    module_limit_type F -> module_limit_type G :=
  module_hom_fun (fmap (module_limit_functor R C) t).

Lemma limit_action_linear {F G : module_diagram R C} (t : nat_trans F G) :
    linear (limit_action t).
Proof. exact (module_hom_linear (fmap (module_limit_functor R C) t)). Qed.

HB.instance Definition _ (F G : module_diagram R C) (t : nat_trans F G) :=
  GRing.isLinear.Build R (module_limit_type F) (module_limit_type G) _
    (limit_action t) (limit_action_linear t).

Lemma limit_action_coordinate {F G : module_diagram R C} (t : nat_trans F G)
    (v : module_limit_type F) (x : C) :
    module_limit_val (limit_action t v) x =
    module_hom_fun (component t x) (module_limit_val v x).
Proof.
  exact (f_equal (fun k : module_hom (module_limit_type F) (fobj G x) => k v)
    (limit_map_fac (module_limit F) (module_limit G) t x)).
Qed.

Variable K : @diagram_complex R C.

Lemma limit_d_squared n (v : module_limit_type (diagram_term K n)) :
    limit_action (diagram_d K n.+1) (limit_action (diagram_d K n) v) = 0.
Proof.
  apply module_limit_val_injective. apply functional_extensionality_dep. intro x.
  rewrite !limit_action_coordinate.
  exact (@diagram_d2 R C K n x (module_limit_val v x)).
Qed.

Definition limit_complex : @cochain_complex R :=
  @CochainComplex R (fun n => module_limit_type (diagram_term K n))
    (fun n => (limit_action (diagram_d K n) :
      {linear module_limit_type (diagram_term K n) ->
        module_limit_type (diagram_term K n.+1)})) limit_d_squared.

Definition limit_contraction (h : diagram_contraction K) :
    contracting_homotopy limit_complex.
Proof.
  refine (@ContractingHomotopy R limit_complex
    (fun n => (limit_action (diagram_contraction_at h n) :
      {linear module_limit_type (diagram_term K n.+1) ->
        module_limit_type (diagram_term K n)})) _ _).
  - intro v. apply module_limit_val_injective. apply functional_extensionality_dep. intro x.
    change (module_limit_val
      (limit_action (diagram_contraction_at h 0%N) (limit_action (diagram_d K 0%N) v)) x =
      module_limit_val v x).
    rewrite !limit_action_coordinate.
    exact (@diagram_contraction_zero R C K h x (module_limit_val v x)).
  - intros n v. apply module_limit_val_injective.
    change (module_limit_val
      (limit_action (diagram_d K n) (limit_action (diagram_contraction_at h n) v) +
       limit_action (diagram_contraction_at h n.+1) (limit_action (diagram_d K n.+1) v)) =
      module_limit_val v).
    have hv := @module_limit_val_linear R C (diagram_term K n.+1).
    have ha : forall (u w : module_limit_type (diagram_term K n.+1)),
        module_limit_val (u + w) = module_limit_val u + module_limit_val w.
    { intros u w. have hh := hv 1 u w. by rewrite !scale1r in hh. }
    rewrite ha.
    apply functional_extensionality_dep. intro x.
    change (module_limit_val (limit_action (diagram_d K n)
        (limit_action (diagram_contraction_at h n) v)) x +
      module_limit_val (limit_action (diagram_contraction_at h n.+1)
        (limit_action (diagram_d K n.+1) v)) x = module_limit_val v x).
    rewrite !limit_action_coordinate.
    exact (@diagram_contraction_succ R C K h n x (module_limit_val v x)).
Defined.

Theorem exact_injective_limit_acyclic (hK : diagram_all_exact K)
    (hI : forall n, injective_object (functor_category C (module_category R))
      (diagram_term K n)) : all_degree_acyclic limit_complex.
Proof.
  exact (contraction_acyclic (limit_contraction
    (exact_injective_diagram_contractible hK hI))).
Qed.

Corollary exact_injective_limit_cohomology_zero (hK : diagram_all_exact K)
    (hI : forall n, injective_object (functor_category C (module_category R))
      (diagram_term K n)) : forall n (v : cohomology limit_complex n), v = 0.
Proof.
  apply (proj1 (all_degree_acyclic_cohomology limit_complex)).
  exact (exact_injective_limit_acyclic hK hI).
Qed.

End LimitComplex.
