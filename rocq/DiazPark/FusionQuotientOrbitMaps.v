From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionQuotientMaps FusionQuotientConstruction.
Import DPFusion DPFusionQuotientConstruction DPFusionOrbit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionQuotientOrbitMaps.
Section InducedMaps.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.

Lemma descends_unique (P Q : {group coset_of Z})
    (f : DPFusion.map (preimage P) (preimage Q)) (b c : DPFusion.map P Q) :
  descends f b -> descends f c -> b = c.
Proof.
move=> hb hc; apply: DPFusion.map_ext=> q Pq.
have xP := repr_mem cZ Pq.
rewrite -(coset_reprK q) (@descendsE S Z P Q f b hb _ xP)
  (@descendsE S Z P Q f c hc _ xP).
reflexivity.
Qed.

Definition induced_map (P Q : {group coset_of Z})
    (f : DPFusionSystem.arrow F (preimage P) (preimage Q)) : DPFusion.map P Q :=
  xchoose (@exists_descended S F Z cZ P Q (val f) (valP f)).

Lemma induced_map_descends (P Q : {group coset_of Z})
    (f : DPFusionSystem.arrow F (preimage P) (preimage Q)) :
  descends (val f) (induced_map f).
Proof. exact: xchooseP. Qed.

Lemma induced_map_allowed (P Q : {group coset_of Z})
    (f : DPFusionSystem.arrow F (preimage P) (preimage Q)) :
  DPFusionSystem.allowed (system cZ) (induced_map f).
Proof.
apply/existsP; exists (val f); apply/andP; split.
- exact: valP f.
- exact: induced_map_descends.
Qed.

Definition induced_arrow (P Q : {group coset_of Z})
    (f : DPFusionSystem.arrow F (preimage P) (preimage Q)) :
    DPFusionSystem.arrow (system cZ) P Q :=
  Sub (induced_map f) (induced_map_allowed f).

Lemma induced_arrowE (P Q : {group coset_of Z})
    (f : DPFusionSystem.arrow F (preimage P) (preimage Q)) x :
  x \in preimage P ->
  DPFusionOrbit.arrow_value (induced_arrow f) (coset Z x) =
    coset Z (DPFusionOrbit.arrow_value f x).
Proof.
move=> Px; exact: (@descendsE S Z P Q (val f) (induced_map f)
  (induced_map_descends f) x Px).
Qed.

Lemma induced_arrow_surjective (P Q : {group coset_of Z})
    (b : DPFusionSystem.arrow (system cZ) P Q) :
  exists f : DPFusionSystem.arrow F (preimage P) (preimage Q), induced_arrow f = b.
Proof.
have /existsP[f /andP[Ff hf]] := valP b.
exists (Sub f Ff); apply: val_inj.
exact: descends_unique (induced_map_descends (Sub f Ff)) hf.
Qed.

Lemma induced_target_inner (P Q : {group coset_of Z})
    (f g : DPFusionSystem.arrow F (preimage P) (preimage Q)) :
  target_inner f g -> target_inner (induced_arrow f) (induced_arrow g).
Proof.
move=> /exists_inP[r rQ /forall_inP he].
apply/exists_inP; exists (coset Z r).
- by rewrite -(preimage_mem cZ).
- apply/forall_inP=> q Pq; apply/eqP.
  have Px := repr_mem cZ Pq.
  rewrite -(coset_reprK q) !induced_arrowE // (eqP (he _ Px)).
  by rewrite morphJ ?(normZ_all cZ).
Qed.

Definition orbit_map (P Q : {group coset_of Z})
    (f : orbit_hom F (preimage P) (preimage Q)) : orbit_hom (system cZ) P Q :=
  orbit_class (induced_arrow (repr f)).

Lemma orbit_map_class (P Q : {group coset_of Z})
    (f : DPFusionSystem.arrow F (preimage P) (preimage Q)) :
  orbit_map (orbit_class f) = orbit_class (induced_arrow f).
Proof.
apply/orbit_class_eq; apply: induced_target_inner.
exact: representative_related.
Qed.

Lemma orbit_map_surjective (P Q : {group coset_of Z}) :
  forall b : orbit_hom (system cZ) P Q, exists f, orbit_map f = b.
Proof.
move=> b; have [f hf] := induced_arrow_surjective (repr b).
exists (orbit_class f); by rewrite orbit_map_class hf /orbit_class reprK.
Qed.

Lemma induced_arrow_identity (P : {group coset_of Z}) :
  induced_arrow (DPFusionSystem.arrow_identity F (preimage P)) =
    DPFusionSystem.arrow_identity (system cZ) P.
Proof.
apply: DPFusionSystem.arrow_ext=> q Pq.
have Px := repr_mem cZ Pq.
change (arrow_value (induced_arrow (DPFusionSystem.arrow_identity F (preimage P))) q =
  DPFusion.identity P q).
rewrite -(coset_reprK q) induced_arrowE //.
by rewrite /arrow_value /DPFusionSystem.arrow_identity /= !DPFusion.identity_in
  ?(preimage_mem cZ) ?coset_reprK.
Qed.

Lemma induced_arrow_compose (P Q R : {group coset_of Z})
    (f : DPFusionSystem.arrow F (preimage P) (preimage Q))
    (g : DPFusionSystem.arrow F (preimage Q) (preimage R)) :
  induced_arrow (DPFusionSystem.arrow_compose f g) =
  DPFusionSystem.arrow_compose (induced_arrow f) (induced_arrow g).
Proof.
apply: DPFusionSystem.arrow_ext=> q Pq.
have Px := repr_mem cZ Pq.
change (arrow_value (induced_arrow (DPFusionSystem.arrow_compose f g)) q =
  DPFusion.compose (val (induced_arrow f)) (val (induced_arrow g)) q).
rewrite DPFusion.compose_in //.
change (arrow_value (induced_arrow (DPFusionSystem.arrow_compose f g)) q =
  arrow_value (induced_arrow g) (arrow_value (induced_arrow f) q)).
have Qfx := DPFusion.map_into (val f) Px.
rewrite -(coset_reprK q) !induced_arrowE //.
by rewrite /arrow_value /DPFusionSystem.arrow_compose /= DPFusion.compose_in.
Qed.

Lemma orbit_map_identity (P : {group coset_of Z}) :
  orbit_map (orbit_identity F (preimage P)) = orbit_identity (system cZ) P.
Proof. by rewrite /orbit_identity orbit_map_class induced_arrow_identity. Qed.

Lemma orbit_map_compose (P Q R : {group coset_of Z})
    (f : orbit_hom F (preimage P) (preimage Q))
    (g : orbit_hom F (preimage Q) (preimage R)) :
  orbit_map (orbit_compose f g) = orbit_compose (orbit_map f) (orbit_map g).
Proof.
rewrite /orbit_compose orbit_map_class induced_arrow_compose.
by rewrite /orbit_map -orbit_compose_class.
Qed.

End InducedMaps.
End DPFusionQuotientOrbitMaps.
