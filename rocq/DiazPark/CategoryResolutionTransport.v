(** Transport of actual injective resolutions through an exact functor of
    module diagrams. The hypotheses are structural preservation properties;
    concrete Kan and restriction instances are proved separately. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryInjectives ModuleDiagrams HomologicalDiagramInjectives
  CategoryInjectiveResolution CategoryInjectiveResolutionComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Transport.
Variable R : pzRingType.
Variables C D : category.
Variable T : functor (functor_category C (module_category R))
  (functor_category D (module_category R)).

Definition diagram_functor_preserves_zero : Prop := forall (F G : module_diagram R C) x (v : fobj (fobj T F) x),
  module_hom_fun (component (fmap T (diagram_zero F G)) x) v = 0.

Definition diagram_functor_preserves_exact : Prop :=
  forall (F G H : module_diagram R C) (a : nat_trans F G) (b : nat_trans G H),
  (forall x (v : fobj G x), module_hom_fun (component b x) v = 0 <->
    exists u, module_hom_fun (component a x) u = v) ->
  forall x (v : fobj (fobj T G) x), module_hom_fun (component (fmap T b) x) v = 0 <->
    exists u, module_hom_fun (component (fmap T a) x) u = v.

Definition diagram_functor_preserves_injections : Prop :=
  forall (F G : module_diagram R C) (a : nat_trans F G),
  (forall x, injective (module_hom_fun (component a x))) ->
  forall x, injective (module_hom_fun (component (fmap T a) x)).

Hypothesis Tzero : diagram_functor_preserves_zero.

Lemma diagram_functor_composite_zero {F G H : module_diagram R C}
    (a : nat_trans F G) (b : nat_trans G H)
    (h : forall x (v : fobj F x), module_hom_fun (component b x)
      (module_hom_fun (component a x) v) = 0) x (v : fobj (fobj T F) x) :
    module_hom_fun (component (fmap T b) x)
      (module_hom_fun (component (fmap T a) x) v) = 0.
Proof.
have hz : nat_comp a b = diagram_zero F H.
  apply nat_trans_ext; intro y; apply module_hom_ext; intro w; exact: h.
have ht := congr1 (fun t : nat_trans (fobj T F) (fobj T H) =>
  module_hom_fun (component t x) v) (fmap_compose T a b).
transitivity (module_hom_fun (component (fmap T (nat_comp a b)) x) v).
- symmetry; exact ht.
- rewrite hz. exact: Tzero.
Qed.

Definition mapped_diagram_complex (K : @diagram_complex R C) : @diagram_complex R D.
Proof.
refine (@DiagramComplex R D (fun n => fobj T (diagram_term K n))
  (fun n => fmap T (diagram_d K n)) _).
intros n x v. apply diagram_functor_composite_zero.
intros y w. exact (@diagram_d2 R C K n y w).
Defined.

Hypothesis Texact : diagram_functor_preserves_exact.
Hypothesis Tmono : diagram_functor_preserves_injections.
Hypothesis Tinj : forall F,
  injective_object (functor_category C (module_category R)) F ->
  injective_object (functor_category D (module_category R)) (fobj T F).

Definition mapped_injective_resolution {F : module_diagram R C}
    (J : injective_resolution F) : injective_resolution (fobj T F).
Proof.
refine (@Build_injective_resolution R D (fobj T F)
  (mapped_diagram_complex (injective_resolution_complex J))
  (fmap T (injective_resolution_augmentation J)) _ _ _ _ _).
- intro n. apply Tinj. exact: injective_resolution_term_injective.
- apply Tmono. exact: injective_resolution_augmentation_injective.
- intros x v. apply diagram_functor_composite_zero.
  exact: injective_resolution_augmentation_zero.
- apply Texact. exact: injective_resolution_exact_zero.
- intros n x v hv.
  refine (proj1 (@Texact _ _ _ (diagram_d (injective_resolution_complex J) n)
    (diagram_d (injective_resolution_complex J) n.+1) _ x v) hv).
  intros y w; split.
  + exact: injective_resolution_exact_successor.
  + intros [z <-]. exact (@diagram_d2 R C (injective_resolution_complex J) n y z).
Defined.

Definition mapped_diagram_cochain_map {K L : @diagram_complex R C}
    (f : diagram_cochain_map K L) : diagram_cochain_map (mapped_diagram_complex K) (mapped_diagram_complex L).
Proof.
refine (@Build_diagram_cochain_map R D (mapped_diagram_complex K) (mapped_diagram_complex L)
  (fun n => fmap T (diagram_cochain_map_at f n)) _).
intros n x v.
have h : nat_comp (diagram_cochain_map_at f n) (diagram_d L n) =
  nat_comp (diagram_d K n) (diagram_cochain_map_at f n.+1).
  apply nat_trans_ext; intro y; apply module_hom_ext; intro w.
  exact: diagram_cochain_map_commutes.
have ht := congr1 (fun t : nat_trans (fobj T (diagram_term K n)) (fobj T (diagram_term L n.+1)) =>
  module_hom_fun (component t x) v) (congr1 (@fmap _ _ T _ _) h).
rewrite !fmap_compose in ht. exact ht.
Defined.

Definition mapped_injective_resolution_map {F G : module_diagram R C}
    {X : injective_resolution F} {Y : injective_resolution G} {u : nat_trans F G}
    (a : injective_resolution_map X Y u) :
    injective_resolution_map (mapped_injective_resolution X) (mapped_injective_resolution Y) (fmap T u).
Proof.
refine (@Build_injective_resolution_map R D (fobj T F) (fobj T G)
  (mapped_injective_resolution X) (mapped_injective_resolution Y) (fmap T u)
  (mapped_diagram_cochain_map (resolution_map_complex a)) _).
have h := congr1 (@fmap _ _ T _ _) (resolution_map_augmentation a).
rewrite !fmap_compose in h. exact h.
Defined.
End Transport.




