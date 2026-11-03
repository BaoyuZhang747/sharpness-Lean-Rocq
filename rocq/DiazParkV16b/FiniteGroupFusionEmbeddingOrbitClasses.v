(** Actual orbit classes under the faithful-image transport. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import FiniteGroupFusion FiniteGroupFusionEmbedding
  FiniteGroupFusionEmbeddingImage FiniteGroupFusionEmbeddingOrbitMaps
  FiniteGroupFusionEmbeddingOrbitInverse FiniteGroupFusionEmbeddingOrbitRaw.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionOrbit DPFiniteGroupFusionEmbeddingOrbit.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFiniteGroupFusionEmbeddingOrbitClasses.
Section Classes.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Hypothesis injE : 'injm E.
Local Notation T := [the finGroupType of [subg (DPFiniteGroupFusionEmbeddingImage.image_group E)]%type].
Local Notation e := (DPFiniteGroupFusionEmbeddingImage.image_equivalence E).
Local Notation r := (DPFiniteGroupFusionEmbeddingImage.image_inverse injE).
Local Notation er := (DPFiniteGroupFusionEmbeddingImage.image_equivalence_inverse injE).
Local Notation re := (DPFiniteGroupFusionEmbeddingImage.image_inverse_equivalence injE).
Local Notation F := (DPFiniteGroupFusionEmbedding.system E).
Local Notation H := (DPFiniteGroupFusion.system (DPFiniteGroupFusionEmbeddingImage.image_group E)).
Local Notation obj := (forward_subgroup E).

Definition forward_arrow (P Q : {group N}) (f : DPFusionSystem.arrow F P Q) :
  DPFusionSystem.arrow H (obj P) (obj Q) := Sub (forward_raw injE (val f)) (forward_allowed injE (valP f)).

Definition backward_arrow (P Q : {group N}) (f : DPFusionSystem.arrow H (obj P) (obj Q)) :
  DPFusionSystem.arrow F P Q := Sub (backward_raw injE (val f)) (backward_allowed injE (valP f)).

Lemma forward_backward_arrow (P Q : {group N}) (f : DPFusionSystem.arrow H (obj P) (obj Q)) :
  forward_arrow (backward_arrow f) = f.
Proof. apply val_inj; exact: forward_backward_raw. Qed.

Lemma backward_forward_arrow (P Q : {group N}) (f : DPFusionSystem.arrow F P Q) :
  backward_arrow (forward_arrow f) = f.
Proof. apply val_inj; exact: backward_forward_raw. Qed.

Lemma forward_arrow_identity P : forward_arrow (DPFusionSystem.arrow_identity F P) =
  DPFusionSystem.arrow_identity H (obj P).
Proof. apply val_inj; exact: DPFusionGroupIsomorphismMaps.map_identity. Qed.

Lemma forward_arrow_compose (P Q U : {group N})
    (f : DPFusionSystem.arrow F P Q) (g : DPFusionSystem.arrow F Q U) :
  forward_arrow (DPFusionSystem.arrow_compose f g) =
    DPFusionSystem.arrow_compose (forward_arrow f) (forward_arrow g).
Proof. apply val_inj; exact: DPFusionGroupIsomorphismMaps.map_compose. Qed.

Lemma forward_related (P Q : {group N}) (f g : DPFusionSystem.arrow F P Q) :
  target_inner f g -> target_inner (forward_arrow f) (forward_arrow g).
Proof.
move/exists_inP=> [z hz /forall_inP h].
apply/exists_inP; exists (e z); first exact: forward_mem.
apply/forall_inP=> y hy; apply/eqP.
rewrite /arrow_value /forward_arrow /=.
change (forward_raw injE (val g) y = forward_raw injE (val f) y ^ e z).
have hx := forward_repr injE hy.
rewrite -(re y) !forward_rawE //.
have hh := eqP (h (r y) hx).
change (val g (r y) = val f (r y) ^ z) in hh.
rewrite hh.
exact (morphJ e (in_setT _) (in_setT _)).
Qed.

Lemma reflect_related (P Q : {group N}) (f g : DPFusionSystem.arrow F P Q) :
  target_inner (forward_arrow f) (forward_arrow g) -> target_inner f g.
Proof.
move/exists_inP=> [z hz /forall_inP h].
apply/exists_inP; exists (r z); first exact: forward_repr.
apply/forall_inP=> x hx; apply/eqP; apply (can_inj er).
have hh := eqP (h (e x) (forward_mem E hx)).
change (forward_raw injE (val g) (e x) = forward_raw injE (val f) (e x) ^ z) in hh.
rewrite !forward_rawE // in hh.
by rewrite (morphJ e (in_setT _) (in_setT _)) re.
Qed.

Lemma backward_related (P Q : {group N})
    (f g : DPFusionSystem.arrow H (obj P) (obj Q)) :
  target_inner f g -> target_inner (backward_arrow f) (backward_arrow g).
Proof. move=> h; apply reflect_related; by rewrite !forward_backward_arrow. Qed.

Definition forward_orbit (P Q : {group N}) (f : orbit_hom F P Q) : orbit_hom H (obj P) (obj Q) :=
  orbit_class (forward_arrow (repr f)).
Definition backward_orbit (P Q : {group N}) (f : orbit_hom H (obj P) (obj Q)) : orbit_hom F P Q :=
  orbit_class (backward_arrow (repr f)).

Lemma forward_orbit_class (P Q : {group N}) (f : DPFusionSystem.arrow F P Q) :
  forward_orbit (orbit_class f) = orbit_class (forward_arrow f).
Proof. apply/orbit_class_eq; apply forward_related; exact: representative_related. Qed.

Lemma backward_orbit_class (P Q : {group N}) (f : DPFusionSystem.arrow H (obj P) (obj Q)) :
  backward_orbit (orbit_class f) = orbit_class (backward_arrow f).
Proof. apply/orbit_class_eq; apply backward_related; exact: representative_related. Qed.

Lemma forward_backward_orbit (P Q : {group N}) : cancel (@forward_orbit P Q) (@backward_orbit P Q).
Proof. apply: quotW=> f; by rewrite forward_orbit_class backward_orbit_class backward_forward_arrow. Qed.

Lemma backward_forward_orbit (P Q : {group N}) : cancel (@backward_orbit P Q) (@forward_orbit P Q).
Proof. apply: quotW=> f; by rewrite backward_orbit_class forward_orbit_class forward_backward_arrow. Qed.

Lemma forward_orbit_identity P : forward_orbit (orbit_identity F P) = orbit_identity H (obj P).
Proof. by rewrite /orbit_identity forward_orbit_class forward_arrow_identity. Qed.

Lemma forward_orbit_compose (P Q U : {group N}) (f : orbit_hom F P Q) (g : orbit_hom F Q U) :
  forward_orbit (orbit_compose f g) = orbit_compose (forward_orbit f) (forward_orbit g).
Proof.
rewrite /orbit_compose forward_orbit_class forward_arrow_compose.
rewrite /forward_orbit; exact: esym (orbit_compose_class _ _).
Qed.

Lemma backward_orbit_identity P : backward_orbit (orbit_identity H (obj P)) = orbit_identity F P.
Proof.
apply (can_inj (@forward_backward_orbit P P)).
by rewrite backward_forward_orbit forward_orbit_identity.
Qed.

Lemma backward_orbit_compose (P Q U : {group N})
    (f : orbit_hom H (obj P) (obj Q)) (g : orbit_hom H (obj Q) (obj U)) :
  backward_orbit (orbit_compose f g) = orbit_compose (backward_orbit f) (backward_orbit g).
Proof.
apply (can_inj (@forward_backward_orbit P U)).
by rewrite backward_forward_orbit forward_orbit_compose !backward_forward_orbit.
Qed.
End Classes.
End DPFiniteGroupFusionEmbeddingOrbitClasses.
