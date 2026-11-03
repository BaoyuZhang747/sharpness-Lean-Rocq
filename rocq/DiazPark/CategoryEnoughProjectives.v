(** Actual free diagrams: finite sums of representables indexed by any family.
    The construction uses arbitrary module carriers and allows the zero ring. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear
  CategoryInjectives ModuleDiagrams CategoryDiagramCokernel BarFreeModule BarResolutionHom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DiazParkBarResolutionHom.
Local Open Scope ring_scope.

Module DPEnoughProjectives.
Definition epimorphism {C : category} {x y : C} (q : hom C x y) : Prop :=
  forall (z : C) (f g : hom C y z), compose q f = compose q g -> f = g.
Definition projective_object (C : category) (P : C) : Prop :=
  forall (x y : C) (q : hom C x y), epimorphism q ->
    forall a : hom C P y, exists b : hom C P x, compose b q = a.
Arguments projective_object C P : clear implicits.

Section Epis.
Variable R : pzRingType.
Variable C : category.
Variables D E : module_diagram R C.
Variable q : nat_trans D E.
Lemma pointwise_surjective_epi :
  (forall x (v : fobj E x), exists u, module_hom_fun (component q x) u = v) ->
  @epimorphism (functor_category C (module_category R)) D E q.
Proof.
move=> h Z f g e; apply nat_trans_ext=> x; apply module_hom_ext=> v.
have [u <-] := h x v.
exact (congr1 (fun t : nat_trans D Z => module_hom_fun (component t x) u) e).
Qed.
Lemma epi_pointwise_surjective :
  @epimorphism (functor_category C (module_category R)) D E q ->
  forall x (v : fobj E x), exists u, module_hom_fun (component q x) u = v.
Proof.
move=> h x v.
have e : nat_comp q (diagram_cokernel_projection q) =
    nat_comp q (diagram_zero E (diagram_cokernel q)).
  apply nat_trans_ext=> y; apply module_hom_ext=> u.
  exact: diagram_cokernel_zero.
have z := h _ _ _ e.
apply (proj1 (diagram_cokernel_exact q v)).
exact (congr1 (fun t : nat_trans E (diagram_cokernel q) => module_hom_fun (component t x) v) z).
Qed.
End Epis.

Section FreeDiagram.
Variable R : pzRingType.
Variable C : category.
Variable I : Type.
Variable base : I -> C.
Definition free_generator (x : C) := {i : I & hom C (base i) x}.
Definition generator_postcompose x y (f : hom C x y)
    (a : free_generator x) : free_generator y :=
  match a with existT i g => existT _ i (compose g f) end.
Lemma generator_postcompose_id x (a : free_generator x) :
  generator_postcompose (identity x) a = a.
Proof. case: a=> i f; by rewrite /generator_postcompose compose_id_right. Qed.
Lemma generator_postcompose_comp x y z (f : hom C x y) (g : hom C y z)
    (a : free_generator x) :
  generator_postcompose (compose f g) a =
    generator_postcompose g (generator_postcompose f a).
Proof. case: a=> i h; by rewrite /generator_postcompose compose_assoc. Qed.
Definition free_diagram : module_diagram R C.
Proof.
refine (@Build_functor C (module_category R)
  (fun x => free_module R (free_generator x))
  (fun x y f => module_hom_of_linear (free_map R (generator_postcompose f))) _ _).
- move=> x; apply module_hom_ext=> v.
  change (free_map R (generator_postcompose (identity x)) v = v).
  have h : generator_postcompose (identity x) = idfun.
    apply functional_extensionality_dep; exact: generator_postcompose_id.
  by rewrite h free_map_identity.
- move=> x y z f g; apply module_hom_ext=> v.
  change (free_map R (generator_postcompose (compose f g)) v =
    free_map R (generator_postcompose g) (free_map R (generator_postcompose f) v)).
  rewrite -free_map_composition.
  have h : generator_postcompose (compose f g) =
      generator_postcompose g \o generator_postcompose f.
    apply functional_extensionality_dep; exact: generator_postcompose_comp.
  by rewrite h.
Defined.
Definition generator_at (i : I) : fobj free_diagram (base i) :=
  free_basis R (existT _ i (identity (base i))).

Variable D : module_diagram R C.
Variable values : forall i, fobj D (base i).
Definition evaluate_generator x (a : free_generator x) : fobj D x :=
  match a with existT i f => module_hom_fun (fmap D f) (values i) end.
Definition free_diagram_lift_component x : module_hom (fobj free_diagram x) (fobj D x) :=
  module_hom_of_linear (free_lift (@evaluate_generator x)).
Definition free_diagram_lift : nat_trans free_diagram D.
Proof.
refine (@Build_nat_trans C (module_category R) free_diagram D
  free_diagram_lift_component _).
move=> x y f; apply free_module_hom_ext=> a.
change (free_lift (@evaluate_generator y)
  (free_map R (generator_postcompose f) (free_basis R a)) =
  module_hom_fun (fmap D f) (free_lift (@evaluate_generator x) (free_basis R a))).
rewrite free_map_basis !free_lift_basis.
case: a=> i g; change (module_hom_fun (fmap D (compose g f)) (values i) =
  module_hom_fun (fmap D f) (module_hom_fun (fmap D g) (values i))).
by rewrite fmap_compose.
Defined.
Lemma free_diagram_lift_generator i : module_hom_fun (component free_diagram_lift (base i)) (generator_at i) = values i.
Proof.
change (free_lift (@evaluate_generator (base i)) (free_basis R (existT _ i (identity (base i)))) = values i).
rewrite free_lift_basis /evaluate_generator fmap_id; reflexivity.
Qed.
Lemma free_diagram_lift_unique (alpha : nat_trans free_diagram D) :
  (forall i, module_hom_fun (component alpha (base i)) (generator_at i) = values i) -> alpha = free_diagram_lift.
Proof.
move=> h; apply nat_trans_ext=> x; apply free_module_hom_ext=> a.
case: a=> i f.
have n := congr1 (fun k : module_hom (fobj free_diagram (base i)) (fobj D x) =>
  k (generator_at i)) (naturality alpha f).
change (module_hom_fun (component alpha x) (free_map R (generator_postcompose f) (generator_at i)) =
  module_hom_fun (fmap D f) (module_hom_fun (component alpha (base i)) (generator_at i))) in n.
rewrite /generator_at free_map_basis /generator_postcompose compose_id_left h in n.
change (module_hom_fun (component alpha x) (free_basis R (existT _ i f)) =
  free_lift (@evaluate_generator x) (free_basis R (existT _ i f))).
by rewrite free_lift_basis; exact n.
Qed.
End FreeDiagram.

Section Projectivity.
Variable R : pzRingType.
Variable C : category.
Variable I : Type.
Variable base : I -> C.
Lemma free_diagram_projective :
  projective_object (functor_category C (module_category R)) (free_diagram R base).
Proof.
move=> D E q hq alpha.
pose values := fun i => proj1_sig (constructive_indefinite_description
  (@epi_pointwise_surjective R C D E q hq (base i)
    (module_hom_fun (component alpha (base i)) (generator_at R base i)))).
pose beta := free_diagram_lift values.
exists beta; change (nat_comp beta q = alpha).
transitivity (free_diagram_lift
  (fun i => module_hom_fun (component alpha (base i)) (generator_at R base i))).
- apply free_diagram_lift_unique=> i; change (module_hom_fun (component q (base i)) (module_hom_fun (component beta (base i)) (generator_at R base i)) =
    module_hom_fun (component alpha (base i)) (generator_at R base i)).
  rewrite /beta free_diagram_lift_generator /values.
  exact (proj2_sig (constructive_indefinite_description
    (@epi_pointwise_surjective R C D E q hq (base i)
      (module_hom_fun (component alpha (base i)) (generator_at R base i))))).
- symmetry; apply free_diagram_lift_unique=> i; reflexivity.
Qed.
End Projectivity.

Section Enough.
Variable R : pzRingType.
Variable C : category.
Variable D : module_diagram R C.
Definition diagram_element := {x : C & fobj D x}.
Definition element_source (i : diagram_element) := projT1 i.
Definition projective_cover := free_diagram R element_source.
Definition projective_cover_map : nat_trans projective_cover D :=
  free_diagram_lift (fun i : diagram_element => projT2 i).
Lemma projective_cover_surjective x (v : fobj D x) :
  exists u, module_hom_fun (component projective_cover_map x) u = v.
Proof.
exists (generator_at R element_source (existT _ x v)).
exact (@free_diagram_lift_generator R C diagram_element element_source D
  (fun i : diagram_element => projT2 i) (existT _ x v)).
Qed.
Lemma projective_cover_projective :
  projective_object (functor_category C (module_category R)) projective_cover.
Proof. exact: free_diagram_projective. Qed.
Lemma projective_cover_epimorphism :
  @epimorphism (functor_category C (module_category R)) projective_cover D projective_cover_map.
Proof. apply pointwise_surjective_epi; exact: projective_cover_surjective. Qed.
Theorem enough_projectives : exists P : module_diagram R C,
  exists q : nat_trans P D, projective_object (functor_category C (module_category R)) P /\
    @epimorphism (functor_category C (module_category R)) P D q.
Proof. exists projective_cover, projective_cover_map; split;
  [exact: projective_cover_projective | exact: projective_cover_epimorphism]. Qed.
End Enough.
End DPEnoughProjectives.








