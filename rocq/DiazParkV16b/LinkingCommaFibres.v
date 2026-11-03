(** The literal orbit fibre of linking morphisms is a torsor for the
    distinguished target subgroup.  Freeness is derived using centricity,
    not postulated as a stronger linking axiom. *)
From mathcomp Require Import all_boot all_fingroup center.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionCentricCriterion FusionCentricBasics.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem
  LinkingSystemCancellation LinkingOrbitProjection.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingCancellation DPLinkingOrbit.
Local Open Scope group_scope.

Module DPLinkingCommaFibres.
Section Fibres.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Lemma distinguished_compose (P : Obj) (x y : [subg (val P)]) :
    linking_compose L (distinguished L x) (distinguished L y) = distinguished L (x * y).
Proof. symmetry; exact: distinguished_mul. Qed.

Lemma centric_map_centralizer_preimage (P Q : Obj)
    (a : DPFusionSystem.arrow F (val P) (val Q)) (z : [subg (val Q)]) :
    val z \in 'C(DPFusion.image (val a)) ->
    exists x : [subg 'Z(val P)], arrow_element a (center_element x) = z.
Proof.
move=> zC.
have zI : val z \in DPFusion.image (val a).
  exact: subsetP (DPFusionCentricCriterion.centric_self_centralizing
    (DPFusionCentricBasics.centric_image (valP a) (valP P))) _ zC.
have /morphimP[x Px _ hx] := zI.
change (val z = DPFusion.map_fun (val a) x) in hx.
have xC : x \in 'C(val P).
  apply/centP=> y Py.
  apply: (@DPFusion.map_injective S _ _ (val a) _ _ (groupM Px Py) (groupM Py Px)).
  rewrite !DPFusion.map_mul // -hx.
  exact: centP zC _ (DPFusion.image_mem (val a) Py).
have xZ : x \in 'Z(val P) by apply/setIP; split.
exists (Sub x xZ); apply val_inj; exact: esym hx.
Qed.

Theorem distinguished_stabilizer_trivial (P Q : Obj) (f : linking_hom L P Q)
    (z : [subg (val Q)]) : linking_compose L f (distinguished L z) = f -> z = 1.
Proof.
move=> hz.
have hp := congr1 (@linking_projection S F L P Q) hz.
rewrite projection_compose /distinguished projection_transporter in hp.
have hfix : forall x, x \in val P ->
    DPFusion.map_fun (val (linking_projection L f)) x ^ val z =
    DPFusion.map_fun (val (linking_projection L f)) x.
  move=> x Px.
  have he := congr1 (fun a : DPFusionSystem.arrow F (val P) (val Q) =>
    DPFusion.map_fun (val a) x) hp.
  change (DPFusion.map_fun (DPFusion.compose (val (linking_projection L f))
    (DPFusion.conjugation (valP (DPLinkingTransporter.transporter_distinguished z)))) x =
    DPFusion.map_fun (val (linking_projection L f)) x) in he.
  rewrite DPFusion.compose_in // DPFusion.conjugation_in ?DPFusion.map_into // in he.
have zC : val z \in 'C(DPFusion.image (val (linking_projection L f))).
  apply/centP=> y /morphimP[x Px _ ->].
  apply/esym/commgP/conjg_fixP; exact: hfix.
have [x hx] := centric_map_centralizer_preimage zC.
have hxf : linking_compose L (distinguished L (center_element x)) f = f.
  rewrite commutation hx; exact hz.
have hx1 := central_stabilizer_trivial hxf.
apply val_inj.
have he := congr1 (fun y : [subg (val Q)] => val y) hx.
rewrite hx1 in he.
change (DPFusion.map_fun (val (linking_projection L f)) 1 = val z) in he.
rewrite DPFusion.map_one in he; exact: esym he.
Qed.

Theorem distinguished_post_injective (P Q : Obj) (f : linking_hom L P Q) :
    injective (fun z : [subg (val Q)] => linking_compose L f (distinguished L z)).
Proof.
move=> a b hab.
have hh := congr1 (fun t : linking_hom L P Q =>
  linking_compose L t (distinguished L b^-1)) hab.
have hs : linking_compose L f (distinguished L (a * b^-1)) = f.
  rewrite -distinguished_compose -linking_assoc hh linking_assoc distinguished_compose mulgV.
  rewrite distinguished_one; exact: linking_id_right.
have hone := distinguished_stabilizer_trivial hs.
have he := congr1 (fun t : [subg (val Q)] => t * b) hone.
by rewrite -mulgA mulVg mulg1 mul1g in he.
Qed.

Theorem orbit_fiber (P Q : Obj) (f g : linking_hom L P Q) :
    fmap (orbit_projection L) f = fmap (orbit_projection L) g ->
    exists! z : [subg (val Q)], linking_compose L f (distinguished L z) = g.
Proof.
move=> /DPFusionOrbit.orbit_class_eq_iff[r [Qr hr]].
pose rQ : [subg (val Q)] := Sub r Qr.
have hp : linking_projection L (linking_compose L f (distinguished L rQ)) = linking_projection L g.
  rewrite projection_compose /distinguished projection_transporter.
  apply DPFusionSystem.arrow_ext=> x Px.
  rewrite DPFusion.compose_in // DPFusion.conjugation_in ?DPFusion.map_into //.
  exact: esym (hr x Px).
have [z [hz _]] := proj1 (@central_fiber S F L P Q
  (linking_compose L f (distinguished L rQ)) g) hp.
change (linking_compose L (distinguished L (center_element z))
  (linking_compose L f (distinguished L rQ)) = g) in hz.
pose w := arrow_element (linking_projection L f) (center_element z) * rQ.
have hw : linking_compose L f (distinguished L w) = g.
  by rewrite /w -distinguished_compose -linking_assoc -commutation linking_assoc.
exists w; split=> // w' hw'; apply: (@distinguished_post_injective P Q f w w').
by rewrite hw hw'.
Qed.
End Fibres.
End DPLinkingCommaFibres.

Check DPLinkingCommaFibres.orbit_fiber.
Print Assumptions DPLinkingCommaFibres.distinguished_stabilizer_trivial.
Print Assumptions DPLinkingCommaFibres.orbit_fiber.
