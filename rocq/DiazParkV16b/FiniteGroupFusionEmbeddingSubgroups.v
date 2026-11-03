(** Actual subgroup maps and conjugators through a faithful embedding. *)
From mathcomp Require Import all_boot all_fingroup pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionConjugacy.
From DiazParkV16b Require Import FiniteGroupFusionEmbedding FiniteGroupFusionEmbeddingImage.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFiniteGroupFusionEmbeddingImage.
Local Open Scope group_scope.

Module DPFiniteGroupFusionEmbeddingSubgroups.
Section Subgroups.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Hypothesis injE : 'injm E.

Definition lower_function (P Q : {group N})
    (f : DPFusion.map (ambient E P) (ambient E Q)) (x : N) : N := invm injE (f (E x)).

Lemma lower_functionE (P Q : {group N})
    (f : DPFusion.map (ambient E P) (ambient E Q)) x (hx : x \in P) :
  E (lower_function f x) = f (E x).
Proof. exact (ambient_inverseK injE (DPFusion.map_into f (ambient_mem E hx))). Qed.

Lemma lower_function_morph (P Q : {group N}) (f : DPFusion.map (ambient E P) (ambient E Q)) :
  {in P &, {morph lower_function f : x y / x*y}}.
Proof.
move=> x y hx hy; apply (embedding_injective injE).
rewrite (morphM E (in_setT _) (in_setT _)) !lower_functionE ?groupM //.
rewrite (morphM E (in_setT x) (in_setT y)).
exact (DPFusion.map_mul f (ambient_mem E hx) (ambient_mem E hy)).
Qed.

Canonical lower_morphism (P Q : {group N}) (f : DPFusion.map (ambient E P) (ambient E Q)) :=
  Morphism (lower_function_morph f).

Lemma lower_morphism_injective (P Q : {group N}) (f : DPFusion.map (ambient E P) (ambient E Q)) :
  'injm (lower_morphism f).
Proof.
apply/injmP=> x y hx hy he; apply (embedding_injective injE).
have hh := congr1 E he.
change (E (lower_function f x) = E (lower_function f y)) in hh.
rewrite !lower_functionE // in hh.
exact (DPFusion.map_injective (ambient_mem E hx) (ambient_mem E hy) hh).
Qed.

Lemma lower_morphism_range (P Q : {group N}) (f : DPFusion.map (ambient E P) (ambient E Q)) :
  lower_morphism f @* P \subset Q.
Proof.
apply/subsetP=> y /morphimP [x _ hx ->].
exact (ambient_repr injE (DPFusion.map_into f (ambient_mem E hx))).
Qed.

Definition lower (P Q : {group N}) (f : DPFusion.map (ambient E P) (ambient E Q)) : DPFusion.map P Q :=
  DPFusion.of_morphism (lower_morphism_injective f) (lower_morphism_range f).

Lemma lowerE (P Q : {group N}) (f : DPFusion.map (ambient E P) (ambient E Q)) x (hx : x \in P) :
  E (lower f x) = f (E x).
Proof. rewrite DPFusion.of_morphism_in //; exact: lower_functionE. Qed.

Definition conjugation_map (P Q : {group N}) (g : G)
    (h : ambient E P :^ g \subset ambient E Q) : DPFusion.map P Q :=
  lower (DPFusion.conjugation h).

Lemma conjugation_mapE (P Q : {group N}) (g : G)
    (h : ambient E P :^ g \subset ambient E Q) x (hx : x \in P) :
  E (conjugation_map h x) = E x ^ g.
Proof. rewrite /conjugation_map lowerE // DPFusion.conjugation_in //; exact: ambient_mem. Qed.

Lemma conjugation_map_allowed (P Q : {group N}) (g : G)
    (h : ambient E P :^ g \subset ambient E Q) :
    DPFusionSystem.allowed (DPFiniteGroupFusionEmbedding.system E) (conjugation_map h).
Proof. apply/DPFiniteGroupFusionEmbedding.allowedP; exists g; exact: conjugation_mapE. Qed.

Lemma ambient_conjugation_sub (P Q : {group N}) (f : DPFusion.map P Q) (g : G) :
  {in P, forall x, E (f x) = E x ^ g} -> ambient E P :^ g \subset ambient E Q.
Proof.
move=> hg; apply/subsetP=> z /imsetP[y /morphimP[x _ hx ->] ->].
rewrite -(hg x hx); exact (ambient_mem E (DPFusion.map_into f hx)).
Qed.

Lemma ambient_conjugation_image (P Q : {group N}) (f : DPFusion.map P Q) (g : G) :
  {in P, forall x, E (f x) = E x ^ g} -> ambient E P :^ g = ambient E (DPFusion.image f).
Proof.
move=> hg; apply/eqP; rewrite eqEcard; apply/andP; split.
- apply: (@ambient_conjugation_sub P (DPFusion.image f) (DPFusion.to_image f) g).
  move=> x hx; by rewrite DPFusion.to_image_in // hg.
- by rewrite cardJg !(ambient_card injE) DPFusionConjugacy.map_image_card.
Qed.

Lemma conjugateP (P Q : {group N}) :
  reflect (exists g : G, ambient E P :^ g = ambient E Q)
    (DPFusionSystem.conjugate (DPFiniteGroupFusionEmbedding.system E) P Q).
Proof.
apply: (iffP existsP).
- move=> [f /andP[/DPFiniteGroupFusionEmbedding.allowedP[g hg] /eqP hf]].
  exists g; by rewrite (ambient_conjugation_image hg) hf.
- move=> [g hg].
  have h : ambient E P :^ g \subset ambient E Q by rewrite hg.
  exists (conjugation_map h); apply/andP; split; first exact: conjugation_map_allowed.
  apply/eqP; apply (ambient_injective injE); apply val_inj.
  exact (eq_trans (esym (ambient_conjugation_image (conjugation_mapE h))) hg).
Qed.

Lemma conjugate_from (P : {group N}) (g : G) (h : ambient E P :^ g \subset image_group E) :
  DPFusionSystem.conjugate (DPFiniteGroupFusionEmbedding.system E) P
    (from_ambient E (ambient E P :^ g)%G).
Proof. apply/conjugateP; exists g; by rewrite ambient_from. Qed.

Lemma sylow_carrier_pgroup p : p.-Sylow([set: G]) (image_group E) -> p.-group [set: N].
Proof.
move=> hs; have hh := morphim_pgroup (invm injE) (pHall_pgroup hs).
by rewrite im_invm in hh.
Qed.
End Subgroups.
End DPFiniteGroupFusionEmbeddingSubgroups.

Check DPFiniteGroupFusionEmbeddingSubgroups.conjugation_map.
Print Assumptions DPFiniteGroupFusionEmbeddingSubgroups.conjugateP.
Print Assumptions DPFiniteGroupFusionEmbeddingSubgroups.sylow_carrier_pgroup.
