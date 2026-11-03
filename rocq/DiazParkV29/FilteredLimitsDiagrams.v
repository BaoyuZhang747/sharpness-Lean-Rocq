(** Pointwise directed colimits of actual contravariant module diagrams. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryModuleLinear CategoryLimits CategoryColimitMaps.
From DiazParkV29 Require Import FilteredLimitsDirected FilteredLimitsMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFilteredLimits DPFilteredMaps.
Local Open Scope ring_scope.

Module DPFilteredDiagrams.
Section Diagrams.
Variable R : pzRingType.
Variable I : directed_poset.
Variable C : category.
Variable F : functor (stage_category I)
  (functor_category (opposite C) (module_category R)).

Definition pointwise_system (c : C) : directed_module R I.
Proof.
refine (@DirectedModule R I (fun i => fobj (fobj F i) c)
  (fun i j h => module_hom_to_linear (component (fmap F h) c)) _ _).
- move=> i h x.
  replace h with (stage_refl i) by apply Prop_irrelevance.
  change (module_hom_fun (component (fmap F (@identity (stage_category I) i)) c) x = x).
  rewrite fmap_id; reflexivity.
- move=> i j k h g x.
  exact (esym (congr1 (fun a : nat_trans (fobj F i) (fobj F k) => module_hom_fun (component a c) x)
    (fmap_compose F h g))).
Defined.

Definition arrow_family x y (f : hom (opposite C) x y) i :
    {linear dm_value (pointwise_system x) i -> dm_value (pointwise_system y) i} :=
  module_hom_to_linear (fmap (fobj F i) f).

Lemma arrow_family_natural x y (f : hom (opposite C) x y) i j
    (h : stage_le i j) v :
    arrow_family f j (dm_map (pointwise_system x) h v) =
      dm_map (pointwise_system y) h (arrow_family f i v).
Proof.
exact (esym (congr1 (fun a : module_hom (fobj (fobj F i) x) (fobj (fobj F j) y) =>
  module_hom_fun a v) (naturality (fmap F h) f))).
Qed.

Definition pointwise_arrow x y (f : hom (opposite C) x y) :
    module_hom (colimit_module (pointwise_system x)) (colimit_module (pointwise_system y)) :=
  exist _ (direct_limit_map (arrow_family f))
    (@direct_limit_map_linear R I (pointwise_system x) (pointwise_system y)
      (arrow_family f) (@arrow_family_natural x y f)).

Lemma pointwise_arrow_in x y (f : hom (opposite C) x y) i
    (v : fobj (fobj F i) x) :
    pointwise_arrow f (colimit_in (V := pointwise_system x) (i := i) v) =
      colimit_in (V := pointwise_system y) (i := i) (module_hom_fun (fmap (fobj F i) f) v).
Proof.
exact (@direct_limit_map_in R I (pointwise_system x) (pointwise_system y)
  (arrow_family f) (@arrow_family_natural x y f) i v).
Qed.

Definition pointwise_colimit : module_codiagram R C.
Proof.
refine (@Build_functor (opposite C) (module_category R)
  (fun c => colimit_module (pointwise_system c)) (@pointwise_arrow) _ _).
- move=> c; apply module_hom_ext=> q.
  have [i [v <-]] := colimit_in_surjective q.
  rewrite pointwise_arrow_in fmap_id; reflexivity.
- move=> x y z f g; apply module_hom_ext=> q.
  have [i [v <-]] := colimit_in_surjective q.
  change (pointwise_arrow (compose f g) (colimit_in v) =
    pointwise_arrow g (pointwise_arrow f (colimit_in v))).
  rewrite !pointwise_arrow_in fmap_compose; reflexivity.
Defined.

Definition pointwise_leg i : nat_trans (fobj F i) pointwise_colimit.
Proof.
refine (@Build_nat_trans (opposite C) (module_category R) (fobj F i) pointwise_colimit
  (fun c => module_hom_of_linear (@colimit_in R I (pointwise_system c) i)) _).
move=> x y f; apply module_hom_ext=> v.
symmetry; exact: pointwise_arrow_in.
Defined.

Lemma pointwise_leg_natural i j (h : stage_le i j) :
    nat_comp (fmap F h) (pointwise_leg j) = pointwise_leg i.
Proof.
apply nat_trans_ext=> c; apply module_hom_ext=> v.
change (colimit_in (V := pointwise_system c) (dm_map (pointwise_system c) h v) =
  colimit_in (V := pointwise_system c) (i := i) v).
exact: colimit_in_map.
Qed.

Definition diagram_cocone : cocone F pointwise_colimit.
Proof.
refine (@Build_cocone (stage_category I)
  (functor_category (opposite C) (module_category R)) F pointwise_colimit pointwise_leg _).
exact: pointwise_leg_natural.
Defined.

Definition object_cocone (G : module_codiagram R C) (s : cocone F G) c :
    cocone (module_system_functor (pointwise_system c)) (fobj G c).
Proof.
refine (@Build_cocone (stage_category I) (module_category R)
  (module_system_functor (pointwise_system c)) (fobj G c)
  (fun i => component (cocone_leg s i) c) _).
move=> i j h.
apply module_hom_ext=> v.
exact (congr1 (fun a : nat_trans (fobj F i) G => module_hom_fun (component a c) v)
  (cocone_natural s h)).
Defined.

Definition diagram_desc (G : module_codiagram R C) (s : cocone F G) :
    nat_trans pointwise_colimit G.
Proof.
refine (@Build_nat_trans (opposite C) (module_category R) pointwise_colimit G
  (fun c => module_colimit_desc (object_cocone s c)) _).
move=> x y f; apply module_hom_ext=> q.
have [i [v <-]] := colimit_in_surjective q.
change (module_colimit_desc (object_cocone s y) (pointwise_arrow f (colimit_in v)) =
  module_hom_fun (fmap G f) (module_colimit_desc (object_cocone s x) (colimit_in v))).
rewrite pointwise_arrow_in !module_colimit_desc_in.
exact (congr1 (fun a : module_hom (fobj (fobj F i) x) (fobj G y) =>
  module_hom_fun a v) (naturality (cocone_leg s i) f)).
Defined.

Definition diagram_colimit : colimiting_cocone F.
Proof.
refine (@Build_colimiting_cocone (stage_category I)
  (functor_category (opposite C) (module_category R)) F pointwise_colimit
  diagram_cocone (@diagram_desc) _ _).
- move=> G s i; apply nat_trans_ext=> c; apply module_hom_ext=> v.
  exact: module_colimit_desc_in.
- move=> G s f hf; apply nat_trans_ext=> c; apply module_hom_ext=> q.
  have [i [v <-]] := colimit_in_surjective q.
  change (module_hom_fun (component f c) (colimit_in v) =
    module_colimit_desc (object_cocone s c) (colimit_in v)).
  rewrite module_colimit_desc_in.
  exact (congr1 (fun a : nat_trans (fobj F i) G => module_hom_fun (component a c) v) (hf i)).
Defined.

End Diagrams.
End DPFilteredDiagrams.
