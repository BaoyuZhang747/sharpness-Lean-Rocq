From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryFinite CategoryFiniteSpans FusionMaps FusionSystems
  FusionOrbit FusionFiniteCategory FusionCentricRestriction.
Import DPFusionOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricInclusionSpans.
Section Inclusions.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Lemma orbit_inclusion_trans (U V T : {group S}) (sUV : U \subset V) (sVT : V \subset T)
    (sUT : U \subset T) :
  orbit_compose (DPFusionCentricRestriction.orbit_inclusion F sUV)
    (DPFusionCentricRestriction.orbit_inclusion F sVT) =
    DPFusionCentricRestriction.orbit_inclusion F sUT.
Proof.
rewrite /DPFusionCentricRestriction.orbit_inclusion orbit_compose_class.
apply: congr1; apply: DPFusionSystem.arrow_ext=> x Ux.
rewrite /DPFusionSystem.arrow_compose /= DPFusion.compose_in //.
by rewrite !DPFusion.inclusion_in ?(subsetP sUV).
Qed.

Local Notation C := (DPFusionFinite.centric_finite_category F).
Variables P Q : fc_object C.

Definition inclusion_span (U : fc_object C) (sUP : val U \subset val P)
    (alpha : fc_hom C U Q) : finite_span C P Q :=
  existT (fun U => (fc_hom C U P * fc_hom C U Q)%type) U
    (DPFusionCentricRestriction.orbit_inclusion F sUP,alpha).

Definition inclusion_span_factor (U V : fc_object C)
    (sUP : val U \subset val P) (sVP : val V \subset val P)
    (alpha : fc_hom C U Q) (beta : fc_hom C V Q)
    (sUV : val U \subset val V)
    (heq : orbit_compose (DPFusionCentricRestriction.orbit_inclusion F sUV) beta = alpha) :
  span_factor (inclusion_span sUP alpha) (inclusion_span sVP beta).
Proof.
exists (DPFusionCentricRestriction.orbit_inclusion F sUV); apply/andP; split; apply/eqP.
- exact: orbit_inclusion_trans.
- exact heq.
Defined.

Lemma inclusion_span_factor_trans (U V T : fc_object C)
    (sUP : val U \subset val P) (sVP : val V \subset val P) (sTP : val T \subset val P)
    (alpha : fc_hom C U Q) (beta : fc_hom C V Q) (gamma : fc_hom C T Q)
    (sUV : val U \subset val V) (sVT : val V \subset val T) (sUT : val U \subset val T)
    heqUV heqVT heqUT :
  span_factor_compose (@inclusion_span_factor U V sUP sVP alpha beta sUV heqUV)
    (@inclusion_span_factor V T sVP sTP beta gamma sVT heqVT) =
    @inclusion_span_factor U T sUP sTP alpha gamma sUT heqUT.
Proof. apply: val_inj; exact: orbit_inclusion_trans. Qed.

End Inclusions.
End DPFusionCentricInclusionSpans.
