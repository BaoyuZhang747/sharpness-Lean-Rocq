From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionSaturationImage
  FusionConjugacy FusionOrbit FusionOrbitRanks FusionCentricBasics FusionCentricRestriction.
Import DPFusion DPFusionOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricSpanNormalization.
Section Normalization.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Lemma adjust_raw_factor (X A P : {group S})
    (h : DPFusionSystem.arrow F X A) (a : DPFusionSystem.arrow F A P)
    (f : DPFusionSystem.arrow F X P) :
  orbit_class (DPFusionSystem.arrow_compose h a) = orbit_class f ->
  exists a' : DPFusionSystem.arrow F A P,
    target_inner a a' /\ DPFusionSystem.arrow_compose h a' = f.
Proof.
move/orbit_class_eq/exists_inP=> [r Pr /forall_inP hr].
have Nr : r \in 'N(P) := subsetP (normG P) r Pr.
have sPP : P :^ r \subset P by rewrite (normP Nr).
pose c : DPFusionSystem.arrow F P P := Sub (DPFusion.conjugation sPP)
  (DPFusionSystem.conjugation_closed F sPP).
pose a' := DPFusionSystem.arrow_compose a c.
exists a'; split.
- apply/exists_inP; exists r=> //; apply/forall_inP=> x Ax.
  by rewrite /a' /arrow_value /DPFusionSystem.arrow_compose /=
    DPFusion.compose_in // DPFusion.conjugation_in ?DPFusion.map_into.
- apply: DPFusionSystem.arrow_ext=> x Xx.
  have hx := eqP (hr x Xx).
  rewrite /arrow_value /DPFusionSystem.arrow_compose /= DPFusion.compose_in // in hx.
  rewrite /a' /c /DPFusionSystem.arrow_compose /= !DPFusion.compose_in ?DPFusion.map_into //.
  rewrite DPFusion.conjugation_in ?DPFusion.map_into //.
Qed.

Lemma composite_image_sub (X A P : {group S})
    (h : DPFusion.map X A) (a : DPFusion.map A P) :
  DPFusion.image (DPFusion.compose h a) \subset DPFusion.image a.
Proof.
apply/subsetP=> y /morphimP[x Xx _ hy].
change (y = DPFusion.compose h a x) in hy.
rewrite hy DPFusion.compose_in //.
exact (@DPFusion.image_mem S A P a (h x) (DPFusion.map_into h Xx)).
Qed.

Definition image_arrow (X P : {group S}) (f : DPFusionSystem.arrow F X P) :
  DPFusionSystem.arrow F X (DPFusion.image (val f)) :=
  Sub (DPFusion.to_image (val f)) (DPFusionSystem.image_closed (valP f)).

Definition orbit_image_iso (X P : {group S}) (f : DPFusionSystem.arrow F X P) :
  @isomorphism (DPFusionOrbit.orbit_category F) X (DPFusion.image (val f)) :=
  @DPFusionRanks.raw_onto_iso S F X (DPFusion.image (val f)) (image_arrow f)
    (DPFusionSaturationImage.image_to_image (val f)).

Lemma orbit_image_factorization (X P : {group S}) (f : DPFusionSystem.arrow F X P) :
  orbit_compose (iso_hom (orbit_image_iso f))
    (DPFusionCentricRestriction.orbit_inclusion F (DPFusion.image_sub (val f))) = orbit_class f.
Proof.
change (orbit_compose (orbit_class (image_arrow f))
    (DPFusionCentricRestriction.orbit_inclusion F (DPFusion.image_sub (val f))) = orbit_class f).
rewrite /DPFusionCentricRestriction.orbit_inclusion orbit_compose_class.
apply: congr1; apply: val_inj; exact: DPFusion.image_factorization.
Qed.

End Normalization.
End DPFusionCentricSpanNormalization.
