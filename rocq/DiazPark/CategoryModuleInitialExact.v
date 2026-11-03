(** Exactness of the actual limit and right Kan functors when the relevant
    indexing categories admit a discrete initial family. *)
From mathcomp Require Import all_ssreflect ssralg boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryInitialFamily CategoryModuleProducts CategoryModuleLimits
  CategoryModuleLimitFunctor CategoryModuleInitialFamily CategoryModuleExactness
  CategoryComma CategoryStructured CategoryModuleRightKan.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ExactLimit.
Variable R : pzRingType.
Variable C : category.
Variable T : initial_family C.
Variables F G H : module_diagram R C.
Variables (a : nat_trans F G) (b : nat_trans G H).

Theorem module_initial_family_limit_exact
    (he : forall x (v : fobj G x),
      module_hom_fun (component b x) v = 0 <->
      exists u, module_hom_fun (component a x) u = v)
    (v : module_limit_type G) :
    module_hom_fun (fmap (module_limit_functor R C) b) v = 0 <->
    exists u, module_hom_fun (fmap (module_limit_functor R C) a) u = v.
Proof.
  apply (@module_exact_iso_transport R
    (module_limit_type F) (module_limit_type G) (module_limit_type H)
    (initial_family_product T F) (initial_family_product T G)
    (initial_family_product T H)
    (module_initial_family_iso T F) (module_initial_family_iso T G)
    (module_initial_family_iso T H)
    (fmap (module_limit_functor R C) a) (fmap (module_limit_functor R C) b)
    (fmap (initial_family_product_functor R T) a)
    (fmap (initial_family_product_functor R T) b)).
  - intro u. exact (f_equal
      (fun k : module_hom (module_limit_type F) (initial_family_product T G) => k u)
      (naturality (iso_hom (module_initial_family_nat_iso R T)) a)).
  - intro u. exact (f_equal
      (fun k : module_hom (module_limit_type G) (initial_family_product T H) => k u)
      (naturality (iso_hom (module_initial_family_nat_iso R T)) b)).
  - intro y. apply module_product_map_exact.
    intros i z. exact (he (initial_family_object T i) z).
Qed.

Theorem module_initial_family_limit_surjective
    (ha : forall x (v : fobj G x),
      exists u, module_hom_fun (component a x) u = v) :
    forall v : module_limit_type G,
      exists u, module_hom_fun (fmap (module_limit_functor R C) a) u = v.
Proof.
  intro v.
  destruct (@module_product_map_surjective R (initial_family_index T)
    (fun i => fobj F (initial_family_object T i))
    (fun i => fobj G (initial_family_object T i))
    (fun i => component a (initial_family_object T i))
    (fun i => ha (initial_family_object T i))
    (module_hom_fun (iso_hom (module_initial_family_iso T G)) v)) as [u hu].
  exists (module_hom_fun (iso_inv (module_initial_family_iso T F)) u).
  apply (@module_iso_hom_injective R _ _ (module_initial_family_iso T G)).
  pose proof (f_equal
    (fun k : module_hom (module_limit_type F) (initial_family_product T G) =>
      k (module_hom_fun (iso_inv (module_initial_family_iso T F)) u))
    (naturality (iso_hom (module_initial_family_nat_iso R T)) a)) as hn.
  transitivity (module_hom_fun
    (fmap (initial_family_product_functor R T) a)
    (module_hom_fun (iso_hom (module_initial_family_iso T F))
      (module_hom_fun (iso_inv (module_initial_family_iso T F)) u))).
  - exact hn.
  - rewrite module_iso_inv_hom_apply. exact hu.
Qed.
End ExactLimit.

Section ExactRan.
Variable R : pzRingType.
Variables C D : category.
Variable L : functor C D.
Variable T : forall d, initial_family (structured_category L d).
Variables F G H : module_diagram R C.
Variables (a : nat_trans F G) (b : nat_trans G H).

Theorem module_ran_initial_family_exact
    (he : forall x (v : fobj G x),
      module_hom_fun (component b x) v = 0 <->
      exists u, module_hom_fun (component a x) u = v)
    (d : D) (v : fobj (fobj (module_ran R L) G) d) :
    module_hom_fun (component (fmap (module_ran R L) b) d) v = 0 <->
    exists u, module_hom_fun (component (fmap (module_ran R L) a) d) u = v.
Proof.
  exact (@module_initial_family_limit_exact R (structured_category L d) (T d)
    (functor_comp (structured_projection L d) F)
    (functor_comp (structured_projection L d) G)
    (functor_comp (structured_projection L d) H)
    (nat_whisker_left (structured_projection L d) a)
    (nat_whisker_left (structured_projection L d) b)
    (fun x => he (structured_source x)) v).
Qed.

Theorem module_ran_initial_family_surjective
    (ha : forall x (v : fobj G x),
      exists u, module_hom_fun (component a x) u = v) :
    forall (d : D) (v : fobj (fobj (module_ran R L) G) d),
      exists u, module_hom_fun (component (fmap (module_ran R L) a) d) u = v.
Proof.
  intros d v.
  exact (@module_initial_family_limit_surjective R (structured_category L d) (T d)
    (functor_comp (structured_projection L d) F)
    (functor_comp (structured_projection L d) G)
    (nat_whisker_left (structured_projection L d) a)
    (fun x => ha (structured_source x)) v).
Qed.
End ExactRan.

