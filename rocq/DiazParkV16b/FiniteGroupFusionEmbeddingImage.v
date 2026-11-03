(** The literal image equivalence and subgroup transport of a faithful
    finite-group embedding. *)
From mathcomp Require Import all_boot all_fingroup.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFiniteGroupFusionEmbeddingImage.
Section Image.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Hypothesis injE : 'injm E.

Lemma embedding_injective : injective E.
Proof. move=> x y; exact: (injmP injE x y (in_setT x) (in_setT y)). Qed.

Definition ambient (P : {group N}) : {group G} := (E @* P)%G.
Definition image_group : {group G} := ambient [set: N]%G.

Lemma ambient_sub (P : {group N}) : ambient P \subset image_group.
Proof. change (E @* P \subset E @* [set: N]); exact (morphimS E (subsetT P)). Qed.

Lemma ambient_mem (P : {group N}) x : x \in P -> E x \in ambient P.
Proof. move=> hx; exact (mem_morphim E (in_setT x) hx). Qed.

Lemma ambient_repr (P : {group N}) y : y \in ambient P -> invm injE y \in P.
Proof. move/morphimP=> [x _ hx ->]; by rewrite invmE ?inE. Qed.

Lemma ambient_inverseK (P : {group N}) y : y \in ambient P -> E (invm injE y) = y.
Proof. move=> hy; exact (invmK injE (subsetP (ambient_sub P) _ hy)). Qed.

Lemma ambient_injective : injective ambient.
Proof.
move=> P Q he; apply val_inj; apply/setP=> x; apply/idP/idP=> hx.
- have h := ambient_mem hx; rewrite he in h; by have := ambient_repr h; rewrite invmE ?inE.
- have h := ambient_mem hx; rewrite -he in h; by have := ambient_repr h; rewrite invmE ?inE.
Qed.

Lemma ambient_card (P : {group N}) : #|ambient P| = #|P|.
Proof. exact (card_injm injE (subsetT P)). Qed.

Lemma ambient_normalizer (P : {group N}) : ambient 'N(P)%G = 'N_image_group(ambient P)%G.
Proof. apply val_inj; exact (injm_norm injE (subsetT P)). Qed.

Lemma ambient_centralizer (P : {group N}) : ambient 'C(P)%G = 'C_image_group(ambient P)%G.
Proof. apply val_inj; exact (injm_cent injE (subsetT P)). Qed.

Definition from_ambient (Q : {group G}) : {group N} := (E @*^-1 Q)%G.

Lemma ambient_from (Q : {group G}) : Q \subset image_group -> ambient (from_ambient Q) = Q.
Proof. move=> hQ; apply val_inj; exact (morphpreK hQ). Qed.

Lemma from_ambientK (P : {group N}) : from_ambient (ambient P) = P.
Proof.
apply ambient_injective; apply ambient_from; exact: ambient_sub.
Qed.

Definition image_equivalence_value (x : N) : [subg image_group] :=
  Sub (E x) (ambient_mem (in_setT x)).

Lemma image_equivalence_value_mul (x y : N) :
  image_equivalence_value (x*y) = image_equivalence_value x * image_equivalence_value y.
Proof. apply val_inj; exact (morphM E (in_setT x) (in_setT y)). Qed.

Definition image_equivalence : {morphism [set: N] >-> [subg image_group]%type}.
Proof.
apply: (Morphism (mfun := image_equivalence_value)); move=> x y _ _.
exact: image_equivalence_value_mul.
Defined.

Definition image_inverse_value (x : [subg image_group]) : N := invm injE (val x).

Lemma image_inverse_value_mul (x y : [subg image_group]) :
  image_inverse_value (x*y) = image_inverse_value x * image_inverse_value y.
Proof. exact (morphM (invm injE) (valP x) (valP y)). Qed.

Definition image_inverse : {morphism [set: [subg image_group]%type] >-> N}.
Proof.
apply: (Morphism (mfun := image_inverse_value)); move=> x y _ _.
exact: image_inverse_value_mul.
Defined.

Theorem image_equivalence_inverse : cancel image_equivalence image_inverse.
Proof. move=> x; exact (invmE injE (in_setT x)). Qed.

Theorem image_inverse_equivalence : cancel image_inverse image_equivalence.
Proof. move=> x; apply val_inj; exact (invmK injE (valP x)). Qed.

Lemma image_equivalence_apply x : val (image_equivalence x) = E x.
Proof. reflexivity. Qed.

End Image.
End DPFiniteGroupFusionEmbeddingImage.

Check DPFiniteGroupFusionEmbeddingImage.image_equivalence.
Print Assumptions DPFiniteGroupFusionEmbeddingImage.image_equivalence_inverse.
Print Assumptions DPFiniteGroupFusionEmbeddingImage.image_inverse_equivalence.
Print Assumptions DPFiniteGroupFusionEmbeddingImage.ambient_normalizer.
