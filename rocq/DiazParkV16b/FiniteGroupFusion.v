(** Fusion induced by an actual finite ambient group on any subgroup.
    Saturation is a separate theorem. Conjugation follows MathComp's
    convention x ^ g = g^-1 * x * g. *)
From mathcomp Require Import all_ssreflect all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionCentralizerMaps.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFiniteGroupFusion.
Section Construction.
Variable G : finGroupType.
Variable T : {group G}.
Local Notation S := [subg T]%type.

Definition allowed (P Q : {group S}) (f : DPFusion.map P Q) :=
  [exists g : G, [forall x in P, val (f x) == (val x) ^ g]].

Lemma allowedP (P Q : {group S}) (f : DPFusion.map P Q) :
  reflect (exists g : G, {in P, forall x, val (f x) = (val x) ^ g})
    (allowed f).
Proof.
apply: (iffP existsP).
- move=> [g /forall_inP hg]; exists g=> x Px; exact: eqP (hg x Px).
- move=> [g hg]; exists g; apply/forall_inP=> x Px; apply/eqP; exact: hg.
Qed.

Lemma conjugation_allowed (P Q : {group S}) (s : S)
    (h : P :^ s \subset Q) : allowed (DPFusion.conjugation h).
Proof.
apply/allowedP; exists (val s)=> x Px.
by rewrite DPFusion.conjugation_in.
Qed.

Lemma composition_allowed (P Q R : {group S})
    (f : DPFusion.map P Q) (h : DPFusion.map Q R) :
  allowed f -> allowed h -> allowed (DPFusion.compose f h).
Proof.
move=> /allowedP[g hg] /allowedP[k hk]; apply/allowedP; exists (g * k)=> x Px.
rewrite DPFusion.compose_in // (hk _ (DPFusion.map_into f Px)) (hg _ Px).
exact: esym (conjgM _ _ _).
Qed.

Lemma image_allowed (P Q : {group S}) (f : DPFusion.map P Q) :
  allowed f -> allowed (DPFusion.to_image f).
Proof.
move=> /allowedP[g hg]; apply/allowedP; exists g=> x Px.
by rewrite DPFusion.to_image_in //; exact: hg.
Qed.

Lemma inverse_allowed (P Q : {group S}) (f : DPFusion.map P Q) :
  allowed f -> allowed (DPFusion.inverse f).
Proof.
move=> /allowedP[g hg]; apply/allowedP; exists g^-1=> y Iy.
have Py := DPFusion.map_into (DPFusion.inverse f) Iy.
have h := congr1 (fun z : G => z ^ g^-1) (hg _ Py).
rewrite DPFusion.inverse_cancel_right // conjgK in h.
exact: esym h.
Qed.

Definition system : DPFusionSystem.system [the finGroupType of S] :=
  @DPFusionSystem.FusionSystem [the finGroupType of S] allowed
    conjugation_allowed composition_allowed image_allowed inverse_allowed.

Lemma system_allowed (P Q : {group S}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed system f = allowed f.
Proof. reflexivity. Qed.

(** An ambient transporter supplies the actual subgroup homomorphism. *)
Definition conjugation_map (P Q : {group S}) (g : G)
    (h : DPFusionSubgroup.ambient P :^ g \subset DPFusionSubgroup.ambient Q) :
    DPFusion.map P Q := DPFusionSubgroup.lower (DPFusion.conjugation h).

Lemma conjugation_mapE (P Q : {group S}) (g : G)
    (h : DPFusionSubgroup.ambient P :^ g \subset DPFusionSubgroup.ambient Q) x :
  x \in P -> val (conjugation_map h x) = (val x) ^ g.
Proof.
move=> Px; rewrite /conjugation_map DPFusionSubgroup.lowerE //.
by rewrite DPFusion.conjugation_in ?DPFusionSubgroup.ambient_mem.
Qed.

Lemma conjugation_map_allowed (P Q : {group S}) (g : G)
    (h : DPFusionSubgroup.ambient P :^ g \subset DPFusionSubgroup.ambient Q) :
  DPFusionSystem.allowed system (conjugation_map h).
Proof. apply/allowedP; exists g; exact: conjugation_mapE. Qed.

Lemma ambient_conjugation_sub (P Q : {group S}) (f : DPFusion.map P Q) (g : G) :
  {in P, forall x, val (f x) = (val x) ^ g} ->
  DPFusionSubgroup.ambient P :^ g \subset DPFusionSubgroup.ambient Q.
Proof.
move=> hg; apply/subsetP=> z /imsetP[y /morphimP[x _ Px ->] ->].
rewrite -(hg _ Px); apply: DPFusionSubgroup.ambient_mem; exact: DPFusion.map_into Px.
Qed.

Lemma conjugation_map_eq (P Q : {group S}) (f : DPFusion.map P Q) (g : G)
    (hg : {in P, forall x, val (f x) = (val x) ^ g}) :
  conjugation_map (ambient_conjugation_sub hg) = f.
Proof.
apply: DPFusion.map_ext=> x Px; apply: val_inj.
by rewrite conjugation_mapE // hg.
Qed.

End Construction.
End DPFiniteGroupFusion.

Print Assumptions DPFiniteGroupFusion.system.
Print Assumptions DPFiniteGroupFusion.conjugation_map_eq.
