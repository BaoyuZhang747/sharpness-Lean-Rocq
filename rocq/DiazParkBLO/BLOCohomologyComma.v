(** The canonical comparison is defined on every actual E3 comma coordinate.
    Its naturality in the elementary subgroup is proved by comma reindexing. *)
From mathcomp Require Import all_boot all_algebra all_fingroup center generic_quotient boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryIsomorphism CategoryReindex
  CategoryModules CategoryModuleLimits CategoryLimits CategoryLimitMaps CategoryStructured
  CategoryRightKan CategoryModuleRightKan CategoryComma
  FusionMaps FusionSystems FusionOrbit FusionCentralizerCover
  FusionCentralizerCoverProjection FusionCentralizerDetectionCover.
From DiazParkV16b Require Import LinkingSystem LinkingSystemFinite LinkingOrbitProjection
  LinkingCommaCategory LinkingCommaNaturality GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyOrbitCoefficient CategoryConstantCohomology.
From DiazParkV28 Require Import FusionCentralizerComma CategoryFiberRanComparison.
From DiazParkBLO Require Import BLODiagram BLOCohomologyDistinguished.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPBLODiagram DPFusionCentralizerCover DPFusionCentralizerCoverProjection
  DPBLOCohomologyDistinguished.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPBLOCohomologyComma.
Section Comma.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Local Notation EC := (elementary_category F p).
Local Notation tau := (DPV28CentralizerComma.tau F p).

Definition comma_enlarged (E : EC) (X : structured_category tau E) :
    enlarged_object F (val E) :=
  @Point S F (val E) (underlying (val (structured_source X)))
    (DPFusionSystem.arrow_compose (structured_arrow X)
      (Sub (DPFusion.inclusion (elementary_center (val (structured_source X))))
        (DPFusionSystem.inclusion_allowed F (elementary_center (val (structured_source X)))))).

Lemma comma_enlarged_alpha (E : EC) (X : structured_category tau E)
    x (hx : x \in val E) :
    val (DPBLODiagram.alpha (comma_enlarged X)) x = val (structured_arrow X) x.
Proof.
rewrite /comma_enlarged /= DPFusion.compose_in // DPFusion.inclusion_in //.
exact: DPFusion.map_into hx.
Qed.

Definition comma_distinguished (E : EC) (X : structured_category tau E) :=
  distinguished_functor L (comma_enlarged X).

Definition comma_linking_arrow (E : EC) (X Y : structured_category tau E)
    (f : hom (structured_category tau E) X Y) :
    hom (enlarged_category L (val E)) (comma_enlarged Y) (comma_enlarged X).
Proof.
pose g := structured_map f.
refine (@Arrow S F L (val E) (comma_enlarged Y) (comma_enlarged X)
  (DPLinkingOrbit.lift_orbit_arrow L (val g)) _).
apply DPFusionSystem.arrow_ext=> x Ex.
rewrite DPFusion.compose_in // !alpha_to_carrierE // !comma_enlarged_alpha //.
rewrite /DPLinkingOrbit.lift_orbit_arrow DPLinkingFinite.chosen_lift_projection.
have he := congr1 (fun a : DPFusionSystem.arrow F (val E)
  (elementary (val (structured_source Y))) => val a x) (structured_commutes f).
change (DPFusion.compose (val (structured_arrow X)) (delta g) x =
  val (structured_arrow Y) x) in he.
rewrite DPFusion.compose_in // in he.
rewrite -he.
exact (@raw_deltaE S F p (val (structured_source Y)) (val (structured_source X))
  (repr (val g)) (valP g) (val (structured_arrow X) x)
  (DPFusion.map_into (val (structured_arrow X)) Ex)).
Defined.

Lemma comma_enlarged_reindex (E E' : EC) (u : hom EC E E')
    (X : structured_category tau E') :
    comma_enlarged (structured_reindex_object tau u X) =
      precompose_object u (comma_enlarged X).
Proof.
rewrite /comma_enlarged /structured_reindex_object /= /precompose_object.
congr (@Point S F (val E) _ _).
exact (@Category.compose_assoc (DPFusionSystem.fusion_category F) _ _ _ _ _ _ _).
Qed.

Lemma comma_distinguished_reindex (E E' : EC) (u : hom EC E E')
    (X : structured_category tau E') :
    comma_distinguished (structured_reindex_object tau u X) =
      functor_comp (comma_distinguished X) (precompose L u).
Proof.
apply (@functor_ext_pointwise _ _
  (comma_distinguished (structured_reindex_object tau u X))
  (functor_comp (comma_distinguished X) (precompose L u))
  (fun _ => comma_enlarged_reindex u X)).
move=> x y g; apply enlarged_hom_ext; rewrite enlarged_transport_map.
have he : f_equal (@DPBLODiagram.underlying S F (val E)) (comma_enlarged_reindex u X) =
    Logic.eq_refl _ := Prop_irrelevance _ _.
rewrite he; reflexivity.
Qed.

Lemma comma_distinguished_forgetful (E : EC) (X : structured_category tau E) :
    functor_comp (comma_distinguished X) (forgetful L (val E)) =
      DPLinkingComma.distinguished_functor L (underlying (val (structured_source X))).
Proof. exact: distinguished_forgetful. Qed.

Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation ambient := (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n).
Local Notation coeff := (@DPFusionCentralizerDetectionCover.centralized_coefficient S F p R ambient).
Local Notation comma_coeff := (fun E => functor_comp (structured_projection tau E) coeff).

Definition bar_value (E : EC) := DPCategoryConstantCohomology.value R A
  (enlarged_category L (val E)) n.

Definition coordinate (E : EC) (X : structured_category tau E) :
    module_hom (bar_value E) (fobj (comma_coeff E) X) :=
  DPCategoryConstantCohomology.pull A (comma_distinguished X) n.

Lemma coordinate_compatible (E : EC) (X Y : structured_category tau E)
    (f : hom (structured_category tau E) X Y) :
    module_hom_comp (coordinate X) (fmap (comma_coeff E) f) = coordinate Y.
Proof.
have h := linking_pull_naturality A (comma_linking_arrow f) n.
change (coordinate Y = module_hom_comp (coordinate X)
  (DPGroupCohomologyPullback.pull A
    (DPLinkingCommaNaturality.arrow_group_hom
      (DPCentricLinking.linking_projection L
        (DPLinkingOrbit.lift_orbit_arrow L (val (structured_map f))))) n)) in h.
rewrite /DPLinkingOrbit.lift_orbit_arrow DPLinkingFinite.chosen_lift_projection in h.
exact: esym h.
Qed.

Definition coordinate_cone (E : EC) : cone (comma_coeff E) (bar_value E) :=
  @Build_cone (structured_category tau E) (module_category R) (comma_coeff E)
    (bar_value E) (@coordinate E) (@coordinate_compatible E).

Definition bar_to_ran (E : EC) :
    module_hom (bar_value E) (fobj (fobj (module_ran R tau) coeff) E) :=
  module_limit_lift (coordinate_cone E).

Lemma bar_to_ran_coordinate (E : EC) (x : bar_value E)
    (X : structured_category tau E) :
    module_limit_val (bar_to_ran E x) X = coordinate X x.
Proof. reflexivity. Qed.

Lemma bar_to_ran_natural (E E' : EC) (u : hom EC E E') :
    module_hom_comp (DPCategoryConstantCohomology.pull A (precompose L u) n)
      (bar_to_ran E') =
    module_hom_comp (bar_to_ran E) (fmap (fobj (module_ran R tau) coeff) u).
Proof.
apply (limit_hom_ext (module_limit (comma_coeff E')))=> X.
rewrite !Category.compose_assoc (ran_arrow_fac tau coeff
  (fun E => module_limit (comma_coeff E)) u X).
apply module_hom_ext=> x.
change (coordinate X (DPCategoryConstantCohomology.pull A (precompose L u) n x) =
  coordinate (structured_reindex_object tau u X) x).
rewrite /coordinate comma_distinguished_reindex DPCategoryConstantCohomology.pull_composition.
reflexivity.
Qed.
End Comma.
End DPBLOCohomologyComma.
