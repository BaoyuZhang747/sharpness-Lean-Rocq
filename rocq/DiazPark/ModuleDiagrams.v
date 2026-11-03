(** Subdiagrams and kernels in the actual category of arbitrary module
    diagrams. These constructions will support natural splittings, rather
    than independently chosen, potentially nonnatural objectwise splittings. *)

From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryInjectives ModuleInjectives ModuleInfrastructure MackeyModuleCarriers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Subdiagrams.
Variable R : pzRingType.
Variable C : category.
Variable F : module_diagram R C.
Variable N : forall x : C, module_subspace (fobj F x).
Hypothesis Nmap : forall (x y : C) (f : hom C x y) (v : fobj F x),
  N x v -> N y (module_hom_fun (fmap F f) v).

Definition subdiagram_object (x : C) : lmodType R :=
  [the lmodType R of submodule_carrier (N x)].

Definition subdiagram_map {x y : C} (f : hom C x y) :
    module_hom (subdiagram_object x) (subdiagram_object y).
Proof.
  exists (fun v => @submodule_in R (fobj F y) (N y)
    (module_hom_fun (fmap F f) (submodule_val v))
    (@Nmap x y f _ (submodule_val_mem v))).
  intros a u v. apply submodule_val_injective.
  change (module_hom_fun (fmap F f) (submodule_val (a *: u + v)) =
    a *: module_hom_fun (fmap F f) (submodule_val u) +
    module_hom_fun (fmap F f) (submodule_val v)).
  rewrite submodule_val_linear.
  apply module_hom_linear.
Defined.

Definition subdiagram : module_diagram R C.
Proof.
  refine (@Build_functor C (module_category R) subdiagram_object
    (fun x y f => subdiagram_map f) _ _).
  - intro x. apply module_hom_ext. intro v. apply submodule_val_injective.
    change (module_hom_fun (fmap F (identity x)) (submodule_val v) = submodule_val v).
    rewrite fmap_id. reflexivity.
  - intros x y z f g. apply module_hom_ext. intro v. apply submodule_val_injective.
    change (module_hom_fun (fmap F (compose f g)) (submodule_val v) =
      module_hom_fun (fmap F g) (module_hom_fun (fmap F f) (submodule_val v))).
    rewrite fmap_compose. reflexivity.
Defined.

Definition subdiagram_inclusion : nat_trans subdiagram F.
Proof.
  refine (@Build_nat_trans C (module_category R) subdiagram F
    (fun x => exist _ (@submodule_val R (fobj F x) (N x))
      (@submodule_val_linear R (fobj F x) (N x))) _).
  intros x y f. apply module_hom_ext. intro v. reflexivity.
Defined.

Lemma subdiagram_inclusion_injective (x : C) :
    injective (module_hom_fun (component subdiagram_inclusion x)).
Proof. exact: submodule_val_injective. Qed.

Definition subdiagram_lift_component (G : module_diagram R C) (t : nat_trans G F)
    (ht : forall x (v : fobj G x), N x (module_hom_fun (component t x) v))
    (x : C) : module_hom (fobj G x) (subdiagram_object x).
Proof.
  exists (fun v => @submodule_in R (fobj F x) (N x)
      (module_hom_fun (component t x) v) (ht x v)).
  intros a u v. apply submodule_val_injective.
  change (module_hom_fun (component t x) (a *: u + v) =
    a *: module_hom_fun (component t x) u + module_hom_fun (component t x) v).
  apply module_hom_linear.
Defined.

Definition subdiagram_lift (G : module_diagram R C) (t : nat_trans G F)
    (ht : forall x (v : fobj G x), N x (module_hom_fun (component t x) v)) :
    nat_trans G subdiagram.
Proof.
  refine (@Build_nat_trans C (module_category R) G subdiagram
    (subdiagram_lift_component ht) _).
  intros x y f. apply module_hom_ext. intro v. apply submodule_val_injective.
  exact (f_equal (fun k : module_hom (fobj G x) (fobj F y) => k v)
    (naturality t f)).
Defined.

Lemma subdiagram_lift_factor (G : module_diagram R C) (t : nat_trans G F)
    (ht : forall x (v : fobj G x), N x (module_hom_fun (component t x) v)) :
    nat_comp (subdiagram_lift ht) subdiagram_inclusion = t.
Proof. apply nat_trans_ext. intro x. apply module_hom_ext. intro v. reflexivity. Qed.

End Subdiagrams.

Arguments subdiagram {R C F} N Nmap.
Arguments subdiagram_inclusion {R C F} N Nmap.

Section DiagramMaps.
Variable R : pzRingType.
Variable C : category.

Definition module_zero_hom (U V : lmodType R) : module_hom U V.
Proof. exists (fun _ => 0). intros a u v. by rewrite scaler0 addr0. Defined.

Definition module_add_hom (U V : lmodType R) (a b : module_hom U V) :
    module_hom U V.
Proof.
  exists (fun v => a v + b v). intros r u v.
  rewrite !module_hom_linear scalerDr. apply addrACA.
Defined.

Definition diagram_zero (F G : module_diagram R C) : nat_trans F G.
Proof.
  refine (@Build_nat_trans C (module_category R) F G
    (fun x => module_zero_hom (fobj F x) (fobj G x)) _).
  intros x y f. apply module_hom_ext. intro v. symmetry. apply module_hom_zero.
Defined.

Definition diagram_add {F G : module_diagram R C} (a b : nat_trans F G) :
    nat_trans F G.
Proof.
  refine (@Build_nat_trans C (module_category R) F G
    (fun x => module_add_hom (component a x) (component b x)) _).
    intros x y f. apply module_hom_ext. intro v.
    pose proof (f_equal (fun k : module_hom (fobj F x) (fobj G y) => k v)
      (naturality a f)) as ha.
    pose proof (f_equal (fun k : module_hom (fobj F x) (fobj G y) => k v)
      (naturality b f)) as hb.
    change (module_hom_fun (component a y) (module_hom_fun (fmap F f) v) +
      module_hom_fun (component b y) (module_hom_fun (fmap F f) v) =
      module_hom_fun (fmap G f)
        (module_hom_fun (component a x) v + module_hom_fun (component b x) v)).
    rewrite module_hom_add. exact (f_equal2 +%R ha hb).
Defined.

Lemma pointwise_injective_monomorphism {F G : module_diagram R C}
    (m : nat_trans F G)
    (hm : forall x, injective (module_hom_fun (component m x))) :
    @monomorphism (functor_category C (module_category R)) F G m.
Proof.
  intros H f g e. apply nat_trans_ext. intro x. apply module_hom_ext. intro v.
  apply (hm x).
  exact (f_equal (fun k : nat_trans H G => module_hom_fun (component k x) v) e).
Qed.

End DiagramMaps.

Section DiagramKernels.
Variable R : pzRingType.
Variable C : category.
Variables F G : module_diagram R C.
Variable t : nat_trans F G.

Definition diagram_kernel_subspace (x : C) : module_subspace (fobj F x).
Proof.
  refine (@ModuleSubspace R (fobj F x)
    (fun v => module_hom_fun (component t x) v = 0) _ _ _).
  - apply module_hom_zero.
  - intros u v hu hv. by rewrite module_hom_add hu hv addr0.
  - intros a v hv. by rewrite module_hom_scale hv scaler0.
Defined.

Lemma diagram_kernel_stable (x y : C) (f : hom C x y) (v : fobj F x) :
    diagram_kernel_subspace x v ->
    diagram_kernel_subspace y (module_hom_fun (fmap F f) v).
Proof.
  intro hv. change (module_hom_fun (component t y) (module_hom_fun (fmap F f) v) = 0).
  transitivity (module_hom_fun (fmap G f) (module_hom_fun (component t x) v)).
  - exact (f_equal (fun k : module_hom (fobj F x) (fobj G y) => k v)
      (naturality t f)).
  - change (module_hom_fun (component t x) v = 0) in hv.
    rewrite hv. apply module_hom_zero.
Qed.

Definition diagram_kernel : module_diagram R C :=
  subdiagram diagram_kernel_subspace diagram_kernel_stable.

Definition diagram_kernel_inclusion : nat_trans diagram_kernel F :=
  subdiagram_inclusion diagram_kernel_subspace diagram_kernel_stable.

Lemma diagram_kernel_inclusion_injective x :
    injective (module_hom_fun (component diagram_kernel_inclusion x)).
Proof. exact: submodule_val_injective. Qed.

Lemma diagram_kernel_zero :
    nat_comp diagram_kernel_inclusion t =
    nat_comp (diagram_zero diagram_kernel F) t.
Proof.
  apply nat_trans_ext. intro x. apply module_hom_ext. intro v.
  change (module_hom_fun (component t x) (submodule_val v) =
    module_hom_fun (component t x) 0).
  rewrite module_hom_zero. exact (submodule_val_mem v).
Qed.

Lemma diagram_monomorphism_pointwise :
    @monomorphism (functor_category C (module_category R)) F G t ->
    forall x, injective (module_hom_fun (component t x)).
Proof.
  intros ht x u v e.
  assert (forall w : fobj F x, module_hom_fun (component t x) w = 0 -> w = 0) as h0.
  { intros w hw.
    pose proof (ht diagram_kernel diagram_kernel_inclusion
      (diagram_zero diagram_kernel F) diagram_kernel_zero) as h.
    pose (z := @submodule_in R (fobj F x) (diagram_kernel_subspace x) w hw).
    exact (f_equal (fun k : nat_trans diagram_kernel F =>
      module_hom_fun (component k x) z) h). }
  apply/eqP. rewrite -subr_eq0. apply/eqP. apply h0.
  by rewrite module_hom_sub e subrr.
Qed.

Lemma diagram_monomorphism_iff :
    @monomorphism (functor_category C (module_category R)) F G t <->
    forall x, injective (module_hom_fun (component t x)).
Proof.
  split. exact diagram_monomorphism_pointwise. apply pointwise_injective_monomorphism.
Qed.

End DiagramKernels.

Theorem module_precomposition_preserves_monomorphisms (R : pzRingType)
    (B C : category) (F : functor B C) :
    preserves_monomorphisms (precomposition (module_category R) F).
Proof.
  intros G H m hm. apply pointwise_injective_monomorphism. intro x.
  exact ((proj1 (diagram_monomorphism_iff m)) hm (fobj F x)).
Qed.
