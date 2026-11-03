From mathcomp Require Import all_boot generic_quotient.
From DiazPark Require Import Category CategoryFiniteProducts.

(** Finite categories retain actual finite object and morphism types.
    Isomorphism classes below are the real quotient by two-sided invertibility,
    not a separately postulated basis set. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope quotient_scope.

Record finite_category := {
  fc_object : finType;
  fc_hom : fc_object -> fc_object -> finType;
  fc_identity : forall x, fc_hom x x;
  fc_compose : forall x y z, fc_hom x y -> fc_hom y z -> fc_hom x z;
  fc_id_left : forall x y (f : fc_hom x y), fc_compose (fc_identity x) f = f;
  fc_id_right : forall x y (f : fc_hom x y), fc_compose f (fc_identity y) = f;
  fc_assoc : forall w x y z (f : fc_hom w x) (g : fc_hom x y) (h : fc_hom y z),
    fc_compose (fc_compose f g) h = fc_compose f (fc_compose g h)
}.

Arguments fc_object _ : clear implicits.
Arguments fc_hom _ _ _ : clear implicits.
Arguments fc_identity {_} _.
Arguments fc_compose {_ _ _ _} _ _.

Definition fc_category (C : finite_category) : category :=
  @Build_category (fc_object C) (fc_hom C) (@fc_identity C)
    (@fc_compose C) (@fc_id_left C) (@fc_id_right C) (@fc_assoc C).

Section FiniteCategory.
Variable C : finite_category.

Definition fc_isomorphic (x y : fc_object C) :=
  [exists f : fc_hom C x y, exists g : fc_hom C y x,
    (fc_compose f g == fc_identity x) && (fc_compose g f == fc_identity y)].

Lemma fc_isomorphic_refl : reflexive fc_isomorphic.
Proof.
move=> x; apply/existsP; exists (fc_identity x); apply/existsP; exists (fc_identity x).
by rewrite fc_id_left eqxx.
Qed.

Lemma fc_isomorphic_sym : symmetric fc_isomorphic.
Proof.
move=> x y; apply/idP/idP;
  move=> /existsP[f /existsP[g /andP[hfg hgf]]];
  apply/existsP; exists g; apply/existsP; exists f; by apply/andP.
Qed.

Lemma fc_isomorphic_trans : transitive fc_isomorphic.
Proof.
move=> x y z /existsP[f /existsP[g /andP[/eqP hfg /eqP hgf]]]
  /existsP[h /existsP[k /andP[/eqP hhk /eqP hkh]]].
apply/existsP; exists (fc_compose f h); apply/existsP; exists (fc_compose k g).
apply/andP; split; apply/eqP.
- by rewrite fc_assoc -[fc_compose h (fc_compose k g)]fc_assoc hhk fc_id_left.
- by rewrite fc_assoc -[fc_compose g (fc_compose f h)]fc_assoc hgf fc_id_left.
Qed.

Definition fc_iso_relation :=
  EquivRel fc_isomorphic fc_isomorphic_refl fc_isomorphic_sym fc_isomorphic_trans.

Definition fc_iso_class := {eq_quot fc_iso_relation}.
Definition fc_class (x : fc_object C) : fc_iso_class := \pi_(fc_iso_class) x.

Lemma fc_class_eq x y : reflect (fc_class x = fc_class y) (fc_isomorphic x y).
Proof. exact: eqmodP. Qed.

Definition fc_iso_of_related (x y : fc_object C) (h : fc_isomorphic x y) :
    @isomorphism (fc_category C) x y.
Proof.
have [f hf] := sigW (existsP h).
have [g /andP[/eqP hfg /eqP hgf]] := sigW (existsP hf).
exact (@Build_isomorphism (fc_category C) x y f g hfg hgf).
Defined.

Lemma fc_related_of_iso (x y : fc_object C) (e : @isomorphism (fc_category C) x y) :
    fc_isomorphic x y.
Proof.
apply/existsP; exists (iso_hom e); apply/existsP; exists (iso_inv e).
apply/andP; split; apply/eqP; [exact (iso_hom_inv e) | exact (iso_inv_hom e)].
Qed.

Lemma fc_class_repr x : fc_class (repr (fc_class x)) = fc_class x.
Proof. exact: reprK. Qed.

Definition fc_repr_iso (x : fc_object C) :
    @isomorphism (fc_category C) (repr (fc_class x)) x :=
  fc_iso_of_related (introT (fc_class_eq _ _) (fc_class_repr x)).

Lemma fc_hom_iso_card (X A B : fc_object C) (e : @isomorphism (fc_category C) A B) :
    #|fc_hom C X A| = #|fc_hom C X B|.
Proof.
apply: (@bij_eq_card (fc_hom C X A) (fc_hom C X B)
  (fun f : fc_hom C X A => fc_compose f (iso_hom e))).
exists (fun f : fc_hom C X B => fc_compose f (iso_inv e)).
- move=> f; have he := iso_hom_inv e.
  change (fc_compose (iso_hom e) (iso_inv e) = fc_identity A) in he.
  by rewrite fc_assoc he fc_id_right.
- move=> f; have he := iso_inv_hom e.
  change (fc_compose (iso_inv e) (iso_hom e) = fc_identity B) in he.
  by rewrite fc_assoc he fc_id_right.
Qed.

Definition fc_mark (X : fc_object C) (a : fc_iso_class) : nat :=
  #|fc_hom C X (repr a)|.

Lemma fc_mark_class X A : fc_mark X (fc_class A) = #|fc_hom C X A|.
Proof. exact: fc_hom_iso_card (fc_repr_iso A). Qed.

Lemma fc_product_cardinality (P Q X : fc_object C)
    (D : @finite_product_decomposition (fc_category C) P Q) :
    (\sum_(i : fp_index D) #|fc_hom C X (fp_apex D i)| =
      #|fc_hom C X P| * #|fc_hom C X Q|)%N.
Proof.
have h : bijective (@fp_encode (fc_category C) P Q X D).
  exists (fun fg => fp_lift D fg.1 fg.2).
  - move=> [i f]; exact: fp_unique.
  - move=> [f g]; exact: fp_encode_lift.
have hcard := bij_eq_card h.
by rewrite card_tagged card_prod sumnE big_map big_enum in hcard.
Qed.

End FiniteCategory.

Print Assumptions fc_iso_of_related.
Print Assumptions fc_repr_iso.
Print Assumptions fc_product_cardinality.
