(** The actual image-prefix coreflection in every linking-evaluation comma. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryComma CategoryAdjunction FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects NormalizerLinkingChainEvaluation
  NormalizerLinkingEvaluationPoints NormalizerLinkingEvaluationPrefixData
  NormalizerLinkingEvaluationProperImage CategoryUniversalCoreflection.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPNormalizerLinkingChainEvaluation
  DPNormalizerLinkingEvaluationPoints DPNormalizerLinkingEvaluationPrefixData
  DPNormalizerLinkingEvaluationProperImage.

Module DPNormalizerLinkingEvaluationCoreflection.
Section Coreflection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable P : DPFusionOrbit.centric_object F.
Local Notation UC := (evaluation_under L P).
Local Notation PT := (evaluation_points L P).
Local Notation J := (points_inclusion L P).

Definition selected_data (X : UC) : prefix_data X.
Proof.
case: (boolP (DPFusion.image (val (linking_projection L (costructured_arrow X))) ==
  val (fobj (evaluation L) (costructured_source X))))=> [/eqP he|hne].
- exact (full_image_data he).
- apply proper_image_data.
  change (DPFusion.image (val (linking_projection L (costructured_arrow X))) \proper
    val (fobj (evaluation L) (costructured_source X))).
  rewrite properEneq DPFusion.image_sub andbT.
  apply/negP=> /eqP he; apply (negP hne); apply/eqP; exact: val_inj he.
Defined.

Definition image_coreflection : functor UC PT :=
  @DPCategoryUniversalCoreflection.coreflection UC PT J
    (fun X => prefix_point (selected_data X))
    (fun X => prefix_deletion (selected_data X))
    (fun X Y f => @prefix_universal S F L P X (selected_data X) Y f).

Definition image_coreflection_adjunction : adjunction J image_coreflection :=
  @DPCategoryUniversalCoreflection.coreflection_adjunction UC PT J
    (fun X => prefix_point (selected_data X))
    (fun X => prefix_deletion (selected_data X))
    (fun X Y f => @prefix_universal S F L P X (selected_data X) Y f).

Lemma image_counit (X : UC) : component (adj_counit image_coreflection_adjunction) X =
  prefix_deletion (selected_data X).
Proof. reflexivity. Qed.
End Coreflection.
End DPNormalizerLinkingEvaluationCoreflection.
