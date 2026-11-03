(** Ordinary finite-group orbit morphisms are actual transporter cosets gK,
    with H^g contained in K. Composition is multiplication of representatives. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPGroupOrbit.
Section Orbit.
Variable G : finGroupType.

Definition transporter (H K : {group G}) := {g : G | H :^ g \subset K}.
Definition related (H K : {group G}) (f g : transporter H K) := val f *: K == val g *: K.
Lemma related_refl (H K : {group G}) : reflexive (@related H K).
Proof. intro f. by rewrite /related eqxx. Qed.
Lemma related_sym (H K : {group G}) : symmetric (@related H K).
Proof. intros f g. by rewrite /related eq_sym. Qed.
Lemma related_trans (H K : {group G}) : transitive (@related H K).
Proof. move=> f g h /eqP hf /eqP hg. by rewrite /related hf hg. Qed.

Definition transporter_equiv (H K : {group G}) :=
  EquivRel (@related H K) (@related_refl H K) (@related_sym H K) (@related_trans H K).
Definition orbit_hom (H K : {group G}) := {eq_quot (transporter_equiv H K)}.
#[export] HB.instance Definition _ (H K : {group G}) := [Finite of orbit_hom H K by <:%/].
Definition orbit_class (H K : {group G}) (f : transporter H K) : orbit_hom H K := \pi_(orbit_hom H K) f.

Lemma orbit_class_eq (H K : {group G}) (f g : transporter H K) :
    reflect (orbit_class f = orbit_class g) (related f g).
Proof. exact: eqmodP. Qed.

Definition transporter_identity (H : {group G}) : transporter H H.
Proof. exists 1. by rewrite conjsg1. Defined.
Definition transporter_compose (H K L : {group G})
    (f : transporter H K) (g : transporter K L) : transporter H L.
Proof.
  exists (val f * val g). rewrite conjsgM.
  have hf : (H :^ val f) :^ val g \subset K :^ val g by rewrite conjSg; exact (valP f).
  exact (subset_trans hf (valP g)).
Defined.

Lemma related_compose (H K L : {group G})
    (f f' : transporter H K) (g g' : transporter K L) :
    related f f' -> related g g' ->
    related (transporter_compose f g) (transporter_compose f' g').
Proof.
  intros hf hg.
  have hff : val f' \in val f *: K by rewrite (eqP hf); exact (lcoset_refl _ _).
  have hgg : val g' \in val g *: L by rewrite (eqP hg); exact (lcoset_refl _ _).
  move/lcosetP: hff => [k hk he]. move/lcosetP: hgg => [l hl he']. 
  apply/eqP. symmetry. apply/lcoset_eqP/lcosetP.
  exists (k ^ (val g) * l).
  - apply groupM. apply (subsetP (valP g)). by rewrite memJ_conjg. exact hl.
  - change (val f' * val g' = (val f * val g) * (k ^ (val g) * l)).
    by rewrite he he' conjgE !mulgA mulgK.
Qed.

Lemma representative_related (H K : {group G}) (f : transporter H K) :
    related (repr (orbit_class f)) f.
Proof. apply/orbit_class_eq. exact (reprK (orbit_class f)). Qed.

Definition orbit_compose (H K L : {group G}) (f : orbit_hom H K) (g : orbit_hom K L) :
    orbit_hom H L := orbit_class (transporter_compose (repr f) (repr g)).
Lemma orbit_compose_class (H K L : {group G}) (f : transporter H K) (g : transporter K L) :
    orbit_compose (orbit_class f) (orbit_class g) = orbit_class (transporter_compose f g).
Proof. apply/orbit_class_eq. apply related_compose; apply representative_related. Qed.
Definition orbit_identity (H : {group G}) := orbit_class (transporter_identity H).

Definition orbit_category : category.
Proof.
  refine (@Build_category {group G} orbit_hom orbit_identity
    (fun H K L f g => orbit_compose f g) _ _ _).
  - intros H K. apply: quotW => f. rewrite /orbit_identity orbit_compose_class.
    congr (orbit_class _). apply val_inj. exact (mul1g (val f)).
  - intros H K. apply: quotW => f. rewrite /orbit_identity orbit_compose_class.
    congr (orbit_class _). apply val_inj. exact (mulg1 (val f)).
  - intros H K L U. apply: quotW => f. apply: quotW => g. apply: quotW => h.
    rewrite (orbit_compose_class f g) (orbit_compose_class g h) !orbit_compose_class.
    congr (orbit_class _). apply val_inj. exact (esym (mulgA (val f) (val g) (val h))).
Defined.

End Orbit.
End DPGroupOrbit.
