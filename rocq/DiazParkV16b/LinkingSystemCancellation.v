(** Every linking morphism is a categorical monomorphism.  The proof
    uses injectivity of actual fusion maps and freeness of the central
    source action; no cancellation property is postulated. *)
From mathcomp Require Import all_boot all_fingroup center.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingTransporter DPCentricLinking.
Local Open Scope group_scope.

Module DPLinkingCancellation.
Section Cancellation.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Lemma center_element_one (P : {group S}) : center_element (1 : [subg 'Z(P)]) = 1.
Proof. apply val_inj; reflexivity. Qed.

Lemma central_stabilizer_trivial (P Q : Obj) (f : linking_hom L P Q)
    (z : [subg 'Z(val P)]) :
    linking_compose L (distinguished L (center_element z)) f = f -> z = 1.
Proof.
move=> hz.
have [w [hw hu]] := proj1 (@central_fiber S F L P Q f f) erefl.
have h1 : linking_compose L (distinguished L (center_element (1 : [subg 'Z(val P)]))) f = f.
  rewrite center_element_one distinguished_one; exact: linking_id_left.
exact (eq_trans (esym (hu z hz)) (hu 1 h1)).
Qed.

Lemma projection_cancel_right (P Q R : Obj)
    (f g : linking_hom L P Q) (h : linking_hom L Q R) :
    linking_compose L f h = linking_compose L g h ->
    linking_projection L f = linking_projection L g.
Proof.
move=> he.
have hp := congr1 (@linking_projection S F L P R) he.
rewrite !projection_compose in hp.
apply DPFusionSystem.arrow_ext => x Px.
apply: (@DPFusion.map_injective S (val Q) (val R) (val (linking_projection L h))
  _ _ (DPFusion.map_into _ Px) (DPFusion.map_into _ Px)).
have hx := congr1 (fun a : DPFusionSystem.arrow F (val P) (val R) =>
  DPFusion.map_fun (val a) x) hp.
change (DPFusion.map_fun (DPFusion.compose (val (linking_projection L f))
    (val (linking_projection L h))) x =
  DPFusion.map_fun (DPFusion.compose (val (linking_projection L g))
    (val (linking_projection L h))) x) in hx.
by rewrite !DPFusion.compose_in in hx.
Qed.

Theorem compose_right_injective (P Q R : Obj) (h : linking_hom L Q R) :
    injective (fun f : linking_hom L P Q => linking_compose L f h).
Proof.
move=> f g he.
have hp := projection_cancel_right he.
have [z [hz _]] := proj1 (@central_fiber S F L P Q f g) hp.
change (linking_compose L (distinguished L (center_element z)) f = g) in hz.
have hfix : linking_compose L (distinguished L (center_element z))
    (linking_compose L f h) = linking_compose L f h.
  by rewrite -linking_assoc hz he.
have hz1 := central_stabilizer_trivial hfix.
rewrite -hz hz1 center_element_one distinguished_one; symmetry; exact: linking_id_left.
Qed.

Theorem category_compose_right_injective (P Q R : linking_category L)
    (h : hom (linking_category L) Q R) :
    injective (fun f : hom (linking_category L) P Q =>
      @compose (linking_category L) P Q R f h).
Proof. exact: compose_right_injective. Qed.
End Cancellation.
End DPLinkingCancellation.

Check DPLinkingCancellation.compose_right_injective.
Print Assumptions DPLinkingCancellation.compose_right_injective.
