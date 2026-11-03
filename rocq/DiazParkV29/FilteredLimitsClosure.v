(** Colimit comparison transported to a specified coefficient diagram. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryFinite CategoryModules CategoryModuleLinear CategoryLimits
  CategoryDerivedLimits ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV29 Require Import FilteredLimitsDirected FilteredLimitsDiagrams
  FilteredLimitsDerived.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFilteredLimits DPFilteredDiagrams DPFilteredDerived.
Local Open Scope ring_scope.

Module DPFilteredClosure.

Section Bijective.
Variable R : pzRingType.
Variables U V : lmodType R.
Variable f : module_hom U V.
Hypothesis fi : injective f.
Hypothesis fs : forall v, exists u, f u = v.

Definition bijective_inverse v : U := proj1_sig (constructive_indefinite_description (fs v)).
Lemma bijective_inverse_right v : f (bijective_inverse v) = v.
Proof. exact: (proj2_sig (constructive_indefinite_description (fs v))). Qed.
Lemma bijective_inverse_left u : bijective_inverse (f u) = u.
Proof. apply fi; exact: bijective_inverse_right. Qed.
Lemma bijective_inverse_linear : linear bijective_inverse.
Proof.
move=> a v w; apply fi.
rewrite bijective_inverse_right module_hom_linear !bijective_inverse_right; reflexivity.
Qed.

Definition module_iso_of_bijective : @isomorphism (module_category R) U V.
Proof.
refine (@Build_isomorphism (module_category R) U V f
  (exist _ bijective_inverse bijective_inverse_linear) _ _).
- apply module_hom_ext=> u; exact: bijective_inverse_left.
- apply module_hom_ext=> v; exact: bijective_inverse_right.
Defined.
End Bijective.

Definition pointwise_bijective_nat_iso (R : pzRingType) (C : category)
    (F G : module_diagram R C) (a : nat_trans F G)
    (hi : forall c, injective (module_hom_fun (component a c)))
    (hs : forall c v, exists u, module_hom_fun (component a c) u = v) :
    @isomorphism (functor_category C (module_category R)) F G :=
  @nat_iso_of_components C (module_category R) F G
    (fun c => module_iso_of_bijective (hi c) (hs c))
    (fun x y f => naturality a f).

Section Transport.
Variable R : pzRingType.
Variable I : directed_poset.
Variable C : finite_category.
Variable F : functor (stage_category I)
  (functor_category (opposite (fc_category C)) (module_category R)).
Variable G : module_codiagram R (fc_category C).
Variable e : @isomorphism (functor_category (opposite (fc_category C)) (module_category R))
  (pointwise_colimit F) G.

Lemma colimit_higher_limit_zero n
    (h : forall i (q : derived_limit R (fobj F i) n), q = 0) :
    forall q : derived_limit R (pointwise_colimit F) n, q = 0.
Proof.
move=> q.
pose ee := higher_limit_colimit_iso F n.
pose u := module_hom_fun (iso_inv ee) q.
have [i [v hv]] := colimit_in_surjective u.
have hz : u = 0 by rewrite -hv (h i v); exact: linear0.
have he := congr1 (fun b : module_hom (derived_limit R (pointwise_colimit F) n)
  (derived_limit R (pointwise_colimit F) n) => module_hom_fun b q) (iso_inv_hom ee).
change (module_hom_fun (iso_hom ee) u = q) in he.
rewrite hz module_hom_zero in he; exact: esym he.
Qed.

Theorem higher_limit_zero_from_stages_and_colimit_iso n
    (h : forall i (q : derived_limit R (fobj F i) n), q = 0) :
    forall q : derived_limit R G n, q = 0.
Proof.
move=> q.
pose ee := functor_iso (derived_limit_functor R (opposite (fc_category C)) n) e.
have hz : module_hom_fun (iso_inv ee) q = 0 := colimit_higher_limit_zero h _.
have he := congr1 (fun b : module_hom (derived_limit R G n) (derived_limit R G n) =>
  module_hom_fun b q) (iso_inv_hom ee).
change (module_hom_fun (iso_hom ee) (module_hom_fun (iso_inv ee) q) = q) in he.
rewrite hz module_hom_zero in he; exact: esym he.
Qed.
End Transport.
End DPFilteredClosure.
