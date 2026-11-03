(** The centraliser-to-enlarged inclusion commutes with the actual
    distinguished group functors and the subgroup embedding used by E3. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryReindex CategoryModules
  FusionMaps FusionSystems FusionSaturation FusionOrbit FusionCentralizer FusionCentralizerMaps
  FusionCentralizerCoverProjection.
From DiazParkV16b Require Import LinkingSystem LinkingCommaCategory
  GroupCohomologyBase GroupCohomologyFunctor GroupCohomologyPullback
  GroupCohomologyEmbeddingDiagramBase CategoryConstantCohomology.
From DiazParkBLO Require Import BLODiagram BLODiagramCentralizerBase
  BLODiagramCentralizerSystem BLODiagramCenterElements BLOCohomologyDistinguished
  BLOCohomologyComma BLOE3Pointwise BLOE3LocalArrow.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPBLODiagram DPBLOCentralizerBase DPBLOCentralizerSystem DPBLOCenterElements
  DPFusionCentralizerCoverProjection DPGroupCohomology DPGroupCohomologyFunctor
  DPGroupCohomologyEmbeddingDiagramBase.
Local Open Scope group_scope.

Module DPBLOCohomologyCentralizerMaps.
Section Centralizer.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable B : elementary_object F p.
Local Notation E := (val B).
Local Notation C := 'C(E)%G.
Local Notation CF := (DPFusionCentralizer.system F E).
Local Notation CL := (@centralizer_linking_system S F L p pS sat B).
Local Notation inc := (@centralizer_inclusion S F L p pS sat B).
Local Notation pt := (@centralizer_point S F p pS sat B).
Local Notation local_comma := (@DPBLOE3Pointwise.local_comma_point S F p pS sat B).

Lemma comma_centralizer_point (P : DPFusionOrbit.centric_object CF) :
    DPBLOCohomologyComma.comma_enlarged (local_comma P) = pt P.
Proof.
have ha : alpha (DPBLOCohomologyComma.comma_enlarged (local_comma P)) = alpha (pt P).
  apply DPFusionSystem.arrow_ext=> x hx.
  by rewrite DPBLOCohomologyComma.comma_enlarged_alpha //
    DPBLOE3LocalArrow.local_comma_arrow_in // centralizer_point_alphaE.
change (@Point S F E (@ambient_object S F p pS sat B P)
  (alpha (DPBLOCohomologyComma.comma_enlarged (local_comma P))) =
  @Point S F E (@ambient_object S F p pS sat B P) (alpha (pt P))).
by rewrite ha.
Qed.

Lemma comma_centralizer_distinguished (P : DPFusionOrbit.centric_object CF) :
    DPBLOCohomologyComma.comma_distinguished L (local_comma P) =
    DPBLOCohomologyDistinguished.distinguished_functor L (pt P).
Proof.
apply (@functor_ext_pointwise _ _
  (DPBLOCohomologyComma.comma_distinguished L (local_comma P))
  (DPBLOCohomologyDistinguished.distinguished_functor L (pt P))
  (fun _ => comma_centralizer_point P)).
move=> x y g; apply enlarged_hom_ext; rewrite enlarged_transport_map.
have he : f_equal (@DPBLODiagram.underlying S F E) (comma_centralizer_point P) =
    Logic.eq_refl _ := Prop_irrelevance _ _.
rewrite he; reflexivity.
Qed.

Definition ambient_group_map (P : DPFusionOrbit.centric_object CF) :=
  subgroup_image_hom [morphism of @sgval S C] (val P).

Lemma ambient_group_map_up (P : DPFusionOrbit.centric_object CF)
    (x : [subg (val P)]) : ambient_group_map P x = subgroup_up x.
Proof. apply val_inj; reflexivity. Qed.

Lemma distinguished_inclusion (P : DPFusionOrbit.centric_object CF) :
    functor_comp (DPLinkingComma.distinguished_functor CL P) inc =
    functor_comp (group_functor (ambient_group_map P))
      (DPBLOCohomologyDistinguished.distinguished_functor L (pt P)).
Proof.
apply (@CategoryIsomorphism.functor_extensionality
  (group_category [subg (val P)]%type) (enlarged_category L E)
  (functor_comp (DPLinkingComma.distinguished_functor CL P) inc)
  (functor_comp (group_functor (ambient_group_map P))
    (DPBLOCohomologyDistinguished.distinguished_functor L (pt P))) (Logic.eq_refl _)).
apply functional_extensionality_dep=> x; apply functional_extensionality_dep=> y.
apply functional_extensionality_dep=> g; apply enlarged_hom_ext.
change (underlying_hom (@DPCentricLinking.distinguished _ _ CL P g) =
  @DPCentricLinking.distinguished S F L (@ambient_object S F p pS sat B P)
    (ambient_group_map P g)).
rewrite ambient_group_map_up.
exact: centralizer_distinguished_underlying.
Qed.

Lemma distinguished_pull_square (R : comPzRingType) (A : lmodType R) n
    (P : DPFusionOrbit.centric_object CF) :
    module_hom_comp (DPCategoryConstantCohomology.pull A inc n)
      (DPCategoryConstantCohomology.pull A (DPLinkingComma.distinguished_functor CL P) n) =
    module_hom_comp (DPCategoryConstantCohomology.pull A
      (DPBLOCohomologyDistinguished.distinguished_functor L (pt P)) n)
      (DPGroupCohomologyPullback.pull A (ambient_group_map P) n).
Proof.
rewrite -DPCategoryConstantCohomology.pull_composition distinguished_inclusion
  DPCategoryConstantCohomology.pull_composition.
reflexivity.
Qed.
End Centralizer.
End DPBLOCohomologyCentralizerMaps.
