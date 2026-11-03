(** Lift a commuting triangle in the raw fusion category uniquely to the
    linking category.  This supplies actual restrictions, rather than an
    additional axiom asserting that restrictions exist. *)
From mathcomp Require Import all_boot all_fingroup center boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem LinkingSystemCancellation.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingTransporter DPCentricLinking DPLinkingCancellation.
Local Open Scope group_scope.

Module DPLinkingFactorization.
Section Factorization.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Lemma projection_central_distinguished (P : Obj) (z : [subg 'Z(val P)]) :
    linking_projection L (distinguished L (center_element z)) =
    DPFusionSystem.arrow_identity F (val P).
Proof.
rewrite /distinguished projection_transporter.
apply val_inj; apply DPFusion.map_ext => x Px.
rewrite DPFusion.conjugation_in // DPFusion.identity_in //.
have zC : val z \in 'C(val P).
  have /setIP[_ hz] := valP z; exact hz.
by rewrite conjgE -(centP zC x Px) mulKg.
Qed.

Lemma projection_central_action (P Q : Obj) (z : [subg 'Z(val P)])
    (f : linking_hom L P Q) :
    linking_projection L (linking_compose L (distinguished L (center_element z)) f) =
    linking_projection L f.
Proof.
rewrite projection_compose projection_central_distinguished.
apply val_inj; exact: DPFusion.identity_compose.
Qed.

Theorem unique_factorization (P Q R : Obj) (f : linking_hom L P Q)
    (g : linking_hom L R Q) (a : DPFusionSystem.arrow F (val P) (val R))
    (ha : DPFusionSystem.arrow_compose a (linking_projection L g) = linking_projection L f) :
    exists! h : linking_hom L P R,
      linking_projection L h = a /\ linking_compose L h g = f.
Proof.
have [h0 hh0] := @projection_surjective S F L P R a.
have hp : linking_projection L (linking_compose L h0 g) = linking_projection L f.
  by rewrite projection_compose hh0 ha.
have [z [hz _]] := proj1 (@central_fiber S F L P Q (linking_compose L h0 g) f) hp.
pose h := linking_compose L (distinguished L (center_element z)) h0.
have hf : linking_compose L h g = f.
  by rewrite /h linking_assoc.
exists h; split.
- split; [by rewrite /h projection_central_action hh0 | exact hf].
- move=> h' [_ hh']; apply: (@compose_right_injective S F L P R Q g).
  by rewrite hf hh'.
Qed.

Definition factorization_lift (P Q R : Obj) (f : linking_hom L P Q)
    (g : linking_hom L R Q) (a : DPFusionSystem.arrow F (val P) (val R))
    (ha : DPFusionSystem.arrow_compose a (linking_projection L g) = linking_projection L f) :
    {h : linking_hom L P R | linking_projection L h = a /\ linking_compose L h g = f}.
Proof.
apply: cid.
have [h [hh _]] := unique_factorization ha; by exists h.
Defined.

Definition factorization (P Q R : Obj) (f : linking_hom L P Q)
    (g : linking_hom L R Q) (a : DPFusionSystem.arrow F (val P) (val R))
    (ha : DPFusionSystem.arrow_compose a (linking_projection L g) = linking_projection L f) :
    linking_hom L P R := proj1_sig (factorization_lift ha).

Lemma factorization_projection (P Q R : Obj) (f : linking_hom L P Q)
    (g : linking_hom L R Q) (a : DPFusionSystem.arrow F (val P) (val R))
    (ha : DPFusionSystem.arrow_compose a (linking_projection L g) = linking_projection L f) :
    linking_projection L (factorization ha) = a.
Proof. exact: (proj1 (proj2_sig (factorization_lift ha))). Qed.

Lemma factorization_commutes (P Q R : Obj) (f : linking_hom L P Q)
    (g : linking_hom L R Q) (a : DPFusionSystem.arrow F (val P) (val R))
    (ha : DPFusionSystem.arrow_compose a (linking_projection L g) = linking_projection L f) :
    linking_compose L (factorization ha) g = f.
Proof. exact: (proj2 (proj2_sig (factorization_lift ha))). Qed.
End Factorization.
End DPLinkingFactorization.

Check DPLinkingFactorization.unique_factorization.
Print Assumptions DPLinkingFactorization.unique_factorization.
Print Assumptions DPLinkingFactorization.factorization_commutes.
