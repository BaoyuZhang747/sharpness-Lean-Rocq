(** Canonical ordinary-limit comparison, with every comma coordinate exposed.
    This identifies the map needed for the native BLO edge, independently of
    the abstract all-degree derived comparison. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryIsomorphism CategoryIsomorphismAdjunction CategoryAdjunction
  CategoryLimits CategoryLimitMaps CategoryLimitFunctor CategoryComma CategoryStructured
  CategoryModules CategoryModuleLimits CategoryModuleLimitFunctor CategoryModuleRightKan
  CategoryRightKanLimits CategoryModuleRightKanLimits CategoryModuleFiberKan
  HomologicalModuleIso FusionSystems FusionSaturation FusionOrbit FusionCentralizer
  FusionCentralizerCover FusionCentralizerCoverOmega FusionCentralizerCoverEquivalence
  FusionCentralizerCoverProjection FusionCentralizerDetectionCover.
From DiazParkV16b Require Import GroupCohomologyOrbitCoefficient.
From DiazParkV28 Require Import CategoryFiberRanComparison FusionCentralizerComma RightKanCohomology.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DPFusionOrbit
  DPFusionCentralizerCoverProjection DPGroupCohomologyOrbitCoefficient.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPBLOE3Limits.

Lemma module_adjoint_limit_coordinate (R : pzRingType) {C D : category}
    {L : functor C D} {T : functor D C} (a : adjunction L T)
    (M : module_diagram R D) (x : C) :
  compose (iso_hom (nat_iso_component (module_left_adjoint_limit_nat_iso R a) M))
    (module_limit_projection (functor_comp L M) x) =
  module_limit_projection M (fobj L x).
Proof.
change (compose (iso_hom (left_adjoint_limit_iso a M (module_limit M)
  (module_limit (functor_comp L M))))
  (cone_leg (limit_cone (module_limit (functor_comp L M))) x) =
  cone_leg (limit_cone (module_limit M)) (fobj L x)).
rewrite left_adjoint_limit_iso_hom; exact: limit_restrict_map_fac.
Qed.

Lemma module_ran_limit_inverse_coordinate (R : pzRingType) {C D : category}
    (L : functor C D) (M : module_diagram R C) (d : D)
    (X : structured_category L d) :
  compose (compose (iso_inv (module_ran_limit_iso R L M))
    (module_limit_projection (fobj (module_ran R L) M) d))
    (module_limit_projection (functor_comp (structured_projection L d) M) X) =
  module_limit_projection M (structured_source X).
Proof.
change (compose (compose
  (limit_map (ran_limit L M
    (fun d => module_limit (functor_comp (structured_projection L d) M)) (module_limit M))
    (module_limit (fobj (module_ran R L) M)) (nat_id _))
  (cone_leg (limit_cone (module_limit (fobj (module_ran R L) M))) d))
  (cone_leg (limit_cone (module_limit (functor_comp (structured_projection L d) M))) X) =
  cone_leg (limit_cone (module_limit M)) (structured_source X)).
rewrite limit_map_fac.
change (compose (compose (cone_leg (@ran_limit_extend C D (module_category R) L M
  (fun d => module_limit (functor_comp (structured_projection L d) M))
  (module_limit_type M) (limit_cone (module_limit M))) d) (identity _))
  (cone_leg (limit_cone (module_limit (functor_comp (structured_projection L d) M))) X) =
  cone_leg (limit_cone (module_limit M)) (structured_source X)).
rewrite compose_id_right; exact: ran_limit_extend_coordinate.
Qed.

Section Cover.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis ntS : [set: S] :!=: 1%G.
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable R : pzRingType.
Variable M : module_codiagram R (centric_orbit_category F).
Local Notation cover := (@DPFusionCentralizerDetectionCover.cover_coefficient S F p R M).
Local Notation central := (@DPFusionCentralizerDetectionCover.centralized_coefficient S F p R M).

Definition centralizer_cover_limit_iso : @isomorphism (module_category R)
  (module_limit_type M) (module_limit_type central) :=
  module_iso_comp
    (nat_iso_component (module_left_adjoint_limit_nat_iso R
      (adjunction_op (@DPFusionCentralizerCoverOmega.section_forget_adjunction S F p pS ntS))) M)
    (nat_iso_component (module_left_adjoint_limit_nat_iso R
      (adjunction_op (@DPFusionCentralizerCoverEquivalence.centralized_inclusion_right_adjoint S F p sat))) cover).

Lemma centralizer_cover_limit_coordinate (x : DPFusionCentralizerCover.centralized_category F p) :
  compose (iso_hom centralizer_cover_limit_iso) (module_limit_projection central x) =
  module_limit_projection M
    (fobj (DPFusionCentralizerCover.forget F p)
      (fobj (DPFusionCentralizerCover.centralized_inclusion F p) x)).
Proof.
change (compose (compose
  (iso_hom (nat_iso_component (module_left_adjoint_limit_nat_iso R
    (adjunction_op (@DPFusionCentralizerCoverOmega.section_forget_adjunction S F p pS ntS))) M))
  (iso_hom (nat_iso_component (module_left_adjoint_limit_nat_iso R
    (adjunction_op (@DPFusionCentralizerCoverEquivalence.centralized_inclusion_right_adjoint S F p sat))) cover)))
  (module_limit_projection central x) = module_limit_projection M
    (fobj (DPFusionCentralizerCover.forget F p)
      (fobj (DPFusionCentralizerCover.centralized_inclusion F p) x))).
rewrite compose_assoc module_adjoint_limit_coordinate.
exact: module_adjoint_limit_coordinate.
Qed.
End Cover.

Section Cohomology.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis ntS : [set: S] :!=: 1%G.
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable n : nat.
Local Notation K := [the fieldType of 'F_p].
Local Notation tau := (DPV28CentralizerComma.tau F p).
Local Notation ambient := (@DPV28RightKanCohomology.ambient_cohomology S F p n).
Local Notation cover := (@DPV28RightKanCohomology.cover_cohomology S F p n).
Local Notation ran := (@DPV28RightKanCohomology.ran_cohomology S F p n).
Local Notation Hn := (@DPV28RightKanCohomology.H_n S F p n).

Definition ambient_to_ran_limit_iso : @isomorphism (module_category K)
  (module_limit_type ambient) (module_limit_type Hn) :=
  module_iso_comp (@centralizer_cover_limit_iso S F p pS ntS sat K ambient)
    (module_iso_comp (iso_symm (module_ran_limit_iso K tau cover))
      (nat_iso_component (module_left_adjoint_limit_nat_iso K
        (category_iso_adjunction
          (DPV28FiberRanComparison.double_opposite_iso (elementary_category F p)))) ran)).

(** At every comma object (P,E',theta:E->E'), the map is the original
    stable family's coordinate at P.  No choice of a centralizer representative
    or varying-E identification is hidden in this formula. *)
Lemma ambient_to_ran_comma_coordinate (B : elementary_object F p)
    (X : structured_category tau B) :
  compose (compose (iso_hom ambient_to_ran_limit_iso) (module_limit_projection Hn B))
    (module_limit_projection (functor_comp (structured_projection tau B) cover) X) =
  module_limit_projection ambient
    (fobj (DPFusionCentralizerCover.forget F p)
      (fobj (DPFusionCentralizerCover.centralized_inclusion F p) (structured_source X))).
Proof.
change (compose (compose (compose
  (iso_hom (@centralizer_cover_limit_iso S F p pS ntS sat K ambient))
  (compose (iso_inv (module_ran_limit_iso K tau cover))
    (iso_hom (nat_iso_component (module_left_adjoint_limit_nat_iso K
      (category_iso_adjunction
        (DPV28FiberRanComparison.double_opposite_iso (elementary_category F p)))) ran))))
  (module_limit_projection Hn B))
  (module_limit_projection (functor_comp (structured_projection tau B) cover) X) =
  module_limit_projection ambient
    (fobj (DPFusionCentralizerCover.forget F p)
      (fobj (DPFusionCentralizerCover.centralized_inclusion F p) (structured_source X)))).
pose a := iso_hom (@centralizer_cover_limit_iso S F p pS ntS sat K ambient).
pose b := iso_inv (module_ran_limit_iso K tau cover).
pose c := iso_hom (nat_iso_component (module_left_adjoint_limit_nat_iso K
  (category_iso_adjunction
    (DPV28FiberRanComparison.double_opposite_iso (elementary_category F p)))) ran).
pose d := module_limit_projection Hn B.
pose e := module_limit_projection (functor_comp (structured_projection tau B) cover) X.
have hc : compose c d = module_limit_projection ran B :=
  @module_adjoint_limit_coordinate K _ _ _ _
    (category_iso_adjunction
      (DPV28FiberRanComparison.double_opposite_iso (elementary_category F p))) ran B.
rewrite (compose_assoc a (compose b c) d) (compose_assoc b c d) hc.
rewrite (compose_assoc a (compose b (module_limit_projection ran B)) e).
rewrite (@module_ran_limit_inverse_coordinate K _ _ tau cover B X).
exact: centralizer_cover_limit_coordinate.
Qed.

Lemma ambient_to_ran_comma_value (x : module_limit_type ambient)
    (B : elementary_object F p) (X : structured_category tau B) :
  module_limit_val (module_limit_val
    ((iso_hom ambient_to_ran_limit_iso : module_hom (module_limit_type ambient) (module_limit_type Hn)) x) B) X =
  module_limit_val x
    (fobj (DPFusionCentralizerCover.forget F p)
      (fobj (DPFusionCentralizerCover.centralized_inclusion F p) (structured_source X))).
Proof. exact (congr1 (fun f : module_hom _ _ => f x) (ambient_to_ran_comma_coordinate X)). Qed.

End Cohomology.
End DPBLOE3Limits.
