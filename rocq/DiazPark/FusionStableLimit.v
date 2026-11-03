(** The actual compatible-family module over the centric orbit category is
    linearly isomorphic to the submodule of stable elements at the Sylow group. *)

From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup boolp generic_quotient.
From DiazPark Require Import Category CategoryModules CategoryModuleProducts
  CategoryModuleLimits ModuleInfrastructure MackeyModuleCarriers MackeyPair
  MackeyPairDiagrams FusionMaps FusionSystems FusionConjugacy FusionOrbit
  FusionSaturation FusionAlperinInductionTools FusionStableElements FusionMackeyShape.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionStable.
Local Open Scope group_scope.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Module DPFusionStableLimit.
Section Limit.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_pair R (DPFusionOrbit.orbit_category F).

Definition centric_coefficient : module_codiagram R (DPFusionOrbit.centric_orbit_category F) :=
  functor_comp (functor_op (DPFusionOrbit.centric_inclusion F)) (pair_codiagram M).

Definition centric_top : DPFusionOrbit.centric_object F :=
  Sub [set: S]%G (DPFusionAlperinInductionTools.centric_top F).

Definition limit_at_top := module_limit_projection centric_coefficient centric_top.

Lemma limit_coordinate (y : module_limit_type centric_coefficient)
    (P : {group S}) (hP : DPFusionSystem.centric F P) :
    restrict_top M P (limit_at_top y) = module_limit_val y (Sub P hP).
Proof.
  exact (@module_limit_val_compatible R _ centric_coefficient y centric_top
    (Sub P hP) (DPFusionOrbit.orbit_class (inclusion F (subsetT P)))).
Qed.

Lemma limit_top_invariant (y : module_limit_type centric_coefficient) :
    @centric_invariant S F R M (limit_at_top y).
Proof.
  intros P a hP. rewrite (limit_coordinate y hP).
  exact (@module_limit_val_compatible R _ centric_coefficient y (Sub P hP)
    (Sub P hP) (DPFusionOrbit.orbit_class a)).
Qed.

Definition stable_subspace : module_subspace (pair_value M [set: S]%G).
Proof.
  refine (@ModuleSubspace R _ (@stable_element S F R M) _ _ _).
  - intros P Q f hf. by rewrite /raw_pull /restrict_top !linear0.
  - intros x y hx hy P Q f hf.
    by rewrite /restrict_top !linearD -/restrict_top (hx _ _ _ hf) (hy _ _ _ hf).
  - intros a x hx P Q f hf.
    by rewrite /restrict_top !linearZ /= -/restrict_top (hx _ _ _ hf).
Defined.

Definition stable_module := [the lmodType R of submodule_carrier stable_subspace].

Definition stable_family (x : stable_module) : module_limit_type centric_coefficient.
Proof.
  refine (@submodule_in R (module_product_type (fobj centric_coefficient))
    (module_limit_subspace centric_coefficient)
    (fun P => restrict_top M (val P) (submodule_val x)) _).
  intros P Q f.
  change (pair_pull M f (restrict_top M (val P) (submodule_val x)) =
    restrict_top M (val Q) (submodule_val x)).
  have h := @stable_all_arrows S F R M (submodule_val x)
    (submodule_val_mem x) (val Q) (val P) (repr f).
  by rewrite /raw_pull /DPFusionOrbit.orbit_class reprK in h.
Defined.

Definition stable_to_limit : module_hom stable_module (module_limit_type centric_coefficient).
Proof.
  exists stable_family. intros a x y.
  apply module_limit_val_injective. apply functional_extensionality_dep. intro P.
  change (restrict_top M (val P) (submodule_val (a*:x+y)) =
    a *: restrict_top M (val P) (submodule_val x) + restrict_top M (val P) (submodule_val y)).
  by rewrite submodule_val_linear linearD linearZ.
Defined.

Lemma stable_family_top (x : stable_module) : limit_at_top (stable_to_limit x) = submodule_val x.
Proof.
  change (restrict_top M [set: S]%G (submodule_val x) = submodule_val x).
  have he : inclusion F (subsetT [set: S]%G) = DPFusionSystem.arrow_identity F [set: S]%G.
  { apply DPFusionSystem.arrow_ext. intros s hs.
    rewrite /inclusion /DPFusionMackey.inclusion_arrow /DPFusionSystem.arrow_identity /=.
    by rewrite DPFusion.inclusion_in // DPFusion.identity_in. }
  rewrite /restrict_top he. exact (@pair_pull_id R (DPFusionOrbit.orbit_category F) M _ _).
Qed.

Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.

Definition limit_stable_value (y : module_limit_type centric_coefficient) : stable_module :=
  @submodule_in R _ stable_subspace (limit_at_top y)
    (centric_invariant_stable pS sat (limit_top_invariant y)).

Definition limit_to_stable : module_hom (module_limit_type centric_coefficient) stable_module.
Proof.
  exists limit_stable_value. intros a x y. apply submodule_val_injective.
  change (limit_at_top (a*:x+y) = a *: limit_at_top x + limit_at_top y).
  exact (module_hom_linear limit_at_top a x y).
Defined.

Lemma limit_stable_inverse (y : module_limit_type centric_coefficient) :
    stable_to_limit (limit_to_stable y) = y.
Proof.
  apply module_limit_val_injective. apply functional_extensionality_dep. intro P.
  destruct P as [P hP]. exact (limit_coordinate y hP).
Qed.

Lemma stable_limit_inverse (x : stable_module) : limit_to_stable (stable_to_limit x) = x.
Proof. apply submodule_val_injective. exact (stable_family_top x). Qed.

Theorem stable_limit_iso : @isomorphism (module_category R)
    (module_limit_type centric_coefficient) stable_module.
Proof.
  refine (@Build_isomorphism (module_category R) _ _ limit_to_stable stable_to_limit _ _).
  - apply module_hom_ext. exact limit_stable_inverse.
  - apply module_hom_ext. exact stable_limit_inverse.
Defined.

End Limit.
End DPFusionStableLimit.
