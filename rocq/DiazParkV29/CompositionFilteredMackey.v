(** The directed system consists of actual full Mackey subfunctors with
    finitely generated values, ordered by inclusion. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryModuleLinear CategoryLimits CategoryColimitMaps ModuleInfrastructure
  MackeyStructures MackeySubquotients MackeyModuleCarriers MackeyModuleMaps
  MackeyFiniteGeneration MackeyFusionFiniteGeneration MackeyBarReduction
  FusionMaps FusionSystems FusionOrbit FusionMackeyShape FusionFiniteCategory
  MackeyPair MackeyPairDiagrams MackeyFusionBridge CategoryDerivedLimits CategoryFinite.
From DiazParkV29 Require Import FilteredLimitsDirected FilteredLimitsDiagrams
  FilteredLimitsDerived FilteredLimitsClosure.
From DiazParkV16b Require Import MackeyFixedDegreeClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFilteredLimits DPFilteredDiagrams.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFilteredLimitsMackey.

Section Subspaces.
Variable R : pzRingType.
Variable V : lmodType R.

Lemma subspace_ext (N P : module_subspace V) :
    (forall x, N x <-> P x) -> N = P.
Proof.
case: N => N n0 nD nZ; case: P => P p0 pD pZ /= => h.
have e : N = P.
  apply functional_extensionality_dep=> x; apply propositional_extensionality; exact: h.
subst P; f_equal; apply Prop_irrelevance.
Qed.

Definition subspace_sum (N P : module_subspace V) : module_subspace V.
Proof.
refine (@ModuleSubspace R V (fun z => exists x y, N x /\ P y /\ x+y=z) _ _ _).
- exists 0,0; split; [exact: subspace_zero | split; [exact: subspace_zero | exact: addr0]].
- move=> z t [x [y [hx [hy <-]]]] [u [v [hu [hv <-]]]].
  exists (x+u),(y+v); split; [exact: subspace_add hx hu | split; [exact: subspace_add hy hv | by rewrite addrACA]].
- move=> a z [x [y [hx [hy <-]]]].
  exists (a*:x),(a*:y); split; [exact: subspace_scale hx | split; [exact: subspace_scale hy | by rewrite scalerDr]].
Defined.

Lemma subspace_sum_l (N P : module_subspace V) x : N x -> subspace_sum N P x.
Proof. move=> hx; exists x,0; split=> //; split; [exact: subspace_zero | exact: addr0]. Qed.
Lemma subspace_sum_r (N P : module_subspace V) x : P x -> subspace_sum N P x.
Proof. move=> hx; exists 0,x; split; [exact: subspace_zero | split=> //; exact: add0r]. Qed.

Definition subspace_embed (N P : module_subspace V) (h : forall x, N x -> P x) :
    {linear submodule_carrier N -> submodule_carrier P} :=
  @submodule_map R V V (idfun : {linear V -> V}) N P h.

Lemma subspace_sum_finite (N P : module_subspace V) :
    module_finitely_generated [the lmodType R of submodule_carrier N] ->
    module_finitely_generated [the lmodType R of submodule_carrier P] ->
    module_finitely_generated [the lmodType R of submodule_carrier (subspace_sum N P)].
Proof.
move=> [s hs] [t ht].
pose f := subspace_embed (@subspace_sum_l N P).
pose g := subspace_embed (@subspace_sum_r N P).
exists ([seq f x | x <- s] ++ [seq g x | x <- t]) => z.
have [x [y [hx [hy he]]]] := submodule_val_mem z.
pose u := @submodule_in R V N x hx.
pose v := @submodule_in R V P y hy.
have ez : z = f u + g v.
  apply: submodule_val_injective.
  change (submodule_val z = submodule_inclusion (subspace_sum N P) (f u + g v)).
  rewrite linearD; exact: esym he.
rewrite ez; apply: span_add.
- apply: (@span_mono R _ (fun w => exists a, a \in s /\ f a = w)) (span_linear_image f (hs u)).
  move=> w [a [ha <-]]; by rewrite mem_cat (map_f f ha).
- apply: (@span_mono R _ (fun w => exists a, a \in t /\ g a = w)) (span_linear_image g (ht v)).
  move=> w [a [ha <-]]; by rewrite mem_cat (map_f g ha) orbT.
Qed.
End Subspaces.

Section FullSystem.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_module R (DPFusionMackey.fusion_mackey_shape F).

Definition full_le (N P : mackey_subfunctor M) :=
  forall U x, subfunctor_value N U x -> subfunctor_value P U x.

Lemma full_ext (N P : mackey_subfunctor M) : full_le N P -> full_le P N -> N = P.
Proof.
case: N => N np ns; case: P => P pp ps /= => h g.
have e : N = P.
  apply functional_extensionality_dep=> U; apply subspace_ext=> x; split; [exact: h | exact: g].
subst P; f_equal; apply Prop_irrelevance.
Qed.

Definition full_sum (N P : mackey_subfunctor M) : mackey_subfunctor M.
Proof.
refine (@MackeySubfunctor R _ _ M
  (fun U => subspace_sum (subfunctor_value N U) (subfunctor_value P U)) _ _).
- move=> U V f z [x [y [hx [hy <-]]]].
  exists (mackey_pull M f x),(mackey_pull M f y); split.
  + exact: subfunctor_pull hx.
  + split; [exact: subfunctor_pull hy | by rewrite linearD].
- move=> U V f z [x [y [hx [hy <-]]]].
  exists (mackey_push M f x),(mackey_push M f y); split.
  + exact: subfunctor_push hx.
  + split; [exact: subfunctor_push hy | by rewrite linearD].
Defined.

Definition finite_full := {N : mackey_subfunctor M |
  forall U, module_finitely_generated (mackey_value (subfunctor_mackey N) U)}.
Definition finite_value (i : finite_full) := proj1_sig i.
Definition finite_le (i j : finite_full) := full_le (finite_value i) (finite_value j).

Definition zero_full : mackey_subfunctor M.
Proof.
refine (@MackeySubfunctor R _ _ M (fun U => subspace_zero_space (mackey_value M U)) _ _);
  move=> U V f x hx; change (x=0) in hx; rewrite hx linear0; reflexivity.
Defined.

Lemma zero_full_finite U : module_finitely_generated (mackey_value (subfunctor_mackey zero_full) U).
Proof.
exists [::]=> x.
have e : x=0.
  apply: submodule_val_injective.
  change (submodule_val x = submodule_inclusion (subfunctor_value zero_full U) 0).
  rewrite linear0; have h := submodule_val_mem x; exact h.
rewrite e; exact: span_zero.
Qed.

Definition finite_zero : finite_full := exist _ zero_full zero_full_finite.
Definition finite_sum (i j : finite_full) : finite_full.
Proof.
exists (full_sum (finite_value i) (finite_value j))=> U.
exact: subspace_sum_finite (proj2_sig i U) (proj2_sig j U).
Defined.

Definition finite_poset : directed_poset.
Proof.
refine (@DirectedPoset finite_full finite_le _ _ _ finite_zero _).
- by move=> i U x hx.
- by move=> i j k h g U x hx; apply: g; apply: h.
- move=> [N hN] [P hP] h g; simpl in h,g.
  have e : N = P := @full_ext N P h g; subst P; f_equal; apply Prop_irrelevance.
- move=> i j; exists (finite_sum i j); split=> U x hx.
  + exact: subspace_sum_l hx.
  + exact: subspace_sum_r hx.
Defined.

Definition finite_inclusion (i j : finite_full) (h : finite_le i j) :
    mackey_hom (subfunctor_mackey (finite_value i)) (subfunctor_mackey (finite_value j)).
Proof.
refine (@MackeyHom R _ _ (subfunctor_mackey (finite_value i)) (subfunctor_mackey (finite_value j)) (fun U => subspace_embed (h U)) _ _);
  move=> U V f x; apply: submodule_val_injective; reflexivity.
Defined.

Lemma finite_exhaustion U (x : mackey_value M U) :
    exists i : finite_full, subfunctor_value (finite_value i) U x.
Proof.
pose src := fun _ : S => U.
pose seed := fun _ : S => x.
pose N := @DPMackeyFinite.finitely_generated_mackey S F R M [the finType of (S : Type)] src seed.
have hN P : module_finitely_generated (mackey_value (subfunctor_mackey N) P).
  exact: DPMackeyFinite.generated_values_finitely_generated.
exists (exist _ N hN); exact: (@DPMackeyFinite.finite_seed_contains S F R M [the finType of (S : Type)] src seed 1%g).
Qed.

Section OnCategory.
Variable C : category.
Variable L : functor C (DPFusionOrbit.orbit_category F).

Definition finite_diagram : functor (stage_category finite_poset)
    (functor_category (opposite C) (module_category R)).
Proof.
refine (@Build_functor (stage_category finite_poset)
  (functor_category (opposite C) (module_category R))
  (fun i => mackey_codiagram L (subfunctor_mackey (finite_value i)))
  (fun i j h => mackey_codiagram_map L (finite_inclusion h)) _ _).
- move=> i; apply nat_trans_ext=> U; apply module_hom_ext=> x.
  apply: submodule_val_injective; reflexivity.
- move=> i j k h g; apply nat_trans_ext=> U; apply module_hom_ext=> x.
  apply: submodule_val_injective; reflexivity.
Defined.

Definition ambient_cocone : cocone finite_diagram (mackey_codiagram L M).
Proof.
refine (@Build_cocone (stage_category finite_poset)
  (functor_category (opposite C) (module_category R)) finite_diagram
  (mackey_codiagram L M)
  (fun i => mackey_codiagram_map L (subfunctor_inclusion (finite_value i))) _).
move=> i j h; apply nat_trans_ext=> U; apply module_hom_ext=> x; reflexivity.
Defined.

Definition colimit_to_ambient := diagram_desc ambient_cocone.

Lemma colimit_to_ambient_in U i (x : mackey_value (subfunctor_mackey (finite_value i)) (fobj L U)) :
    module_hom_fun (component colimit_to_ambient U)
      (colimit_in (V := pointwise_system finite_diagram U) (i := i) x) = submodule_val x.
Proof. exact: module_colimit_desc_in. Qed.

Lemma colimit_to_ambient_injective U :
    injective (module_hom_fun (component colimit_to_ambient U)).
Proof.
move=> x y; have [i [a <-]] := colimit_in_surjective x.
have [j [b <-]] := colimit_in_surjective y.
rewrite !colimit_to_ambient_in => he.
apply/colimit_in_eq.
exists (upper i j), (le_upper_l i j), (le_upper_r i j).
apply: submodule_val_injective; exact he.
Qed.

Lemma colimit_to_ambient_surjective U (x : mackey_value M (fobj L U)) :
    exists q, module_hom_fun (component colimit_to_ambient U) q = x.
Proof.
have [i hi] := finite_exhaustion x.
exists (colimit_in (V := pointwise_system finite_diagram U) (i := i) (submodule_in hi)).
exact: colimit_to_ambient_in.
Qed.

Definition full_subfunctor_colimit_iso :
    @isomorphism (functor_category (opposite C) (module_category R))
      (pointwise_colimit finite_diagram) (mackey_codiagram L M) :=
  DPFilteredClosure.pointwise_bijective_nat_iso
    colimit_to_ambient_injective colimit_to_ambient_surjective.

End OnCategory.

Theorem finite_subfunctor_higher_limit_closure
    (C : finite_category) (L : functor (fc_category C) (DPFusionOrbit.orbit_category F)) n
    (h : forall N : mackey_subfunctor M,
      (forall U, module_finitely_generated (mackey_value (subfunctor_mackey N) U)) ->
      forall q : derived_limit R (mackey_codiagram L (subfunctor_mackey N)) n, q = 0) :
    forall q : derived_limit R (mackey_codiagram L M) n, q = 0.
Proof.
apply: (DPFilteredClosure.higher_limit_zero_from_stages_and_colimit_iso
  (full_subfunctor_colimit_iso L)).
move=> i q; exact: h (proj2_sig i) q.
Qed.

Theorem centric_subfunctor_higher_limit_closure n
    (h : forall N : mackey_subfunctor M,
      (forall U, module_finitely_generated (mackey_value (subfunctor_mackey N) U)) ->
      forall q : derived_limit R
        (mackey_codiagram (DPFusionOrbit.centric_inclusion F) (subfunctor_mackey N)) n, q = 0) :
    forall q : derived_limit R (mackey_codiagram (DPFusionOrbit.centric_inclusion F) M) n, q = 0.
Proof.
exact (@finite_subfunctor_higher_limit_closure
  (DPFusionFinite.centric_finite_category F)
  (functor_comp (DPFusionFinite.finite_to_centric F) (DPFusionOrbit.centric_inclusion F)) n h).
Qed.
End FullSystem.

Theorem inclusion_subfunctor_higher_limit_closure
    (S : finGroupType) (F : DPFusionSystem.system S) (R : comPzRingType)
    (M : mackey_pair R (DPFusionOrbit.orbit_category F))
    (hM : DPMackeyFusion.inclusion_mackey_formula M) n
    (h : forall N : mackey_subfunctor (DPMackeyFusion.full_mackey_of_inclusions hM),
      (forall U, module_finitely_generated (mackey_value (subfunctor_mackey N) U)) ->
      forall q : derived_limit R
        (mackey_codiagram (DPFusionOrbit.centric_inclusion F) (subfunctor_mackey N)) n, q = 0) :
    forall q : derived_limit R
      (pair_codiagram (pair_restrict M (DPFusionOrbit.centric_inclusion F))) n, q = 0.
Proof.
rewrite -(DPMackeyFixedDegree.inclusion_centric_codiagram hM).
exact: centric_subfunctor_higher_limit_closure h.
Qed.

End DPFilteredLimitsMackey.

Check DPFilteredLimitsMackey.full_subfunctor_colimit_iso.
Check DPFilteredLimitsMackey.centric_subfunctor_higher_limit_closure.
Print Assumptions DPFilteredLimitsMackey.full_subfunctor_colimit_iso.
Print Assumptions DPFilteredLimitsMackey.centric_subfunctor_higher_limit_closure.














