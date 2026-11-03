(** Ambient conjugation fusion viewed through a finite-group morphism.
    The later image equivalence uses injectivity; the structural fusion axioms
    themselves hold for every group morphism. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion.
Local Open Scope group_scope.

Module DPFiniteGroupFusionEmbedding.
Section Construction.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.

Definition allowed (P Q : {group N}) (f : DPFusion.map P Q) :=
  [exists g : G, [forall x in P, E (f x) == (E x) ^ g]].

Lemma allowedP (P Q : {group N}) (f : DPFusion.map P Q) : reflect
  (exists g : G, {in P, forall x, E (f x) = (E x) ^ g}) (allowed f).
Proof.
apply: (iffP existsP).
- move=> [g /forall_inP hg]; exists g=> x hx; exact: eqP (hg x hx).
- move=> [g hg]; exists g; apply/forall_inP=> x hx; apply/eqP; exact: hg.
Qed.

Lemma conjugation_allowed (P Q : {group N}) (s : N) (h : P :^ s \subset Q) :
  allowed (DPFusion.conjugation h).
Proof.
apply/allowedP; exists (E s)=> x hx.
by rewrite DPFusion.conjugation_in // morphJ ?inE.
Qed.

Lemma composition_allowed (P Q T : {group N}) (f : DPFusion.map P Q) (g : DPFusion.map Q T) :
  allowed f -> allowed g -> allowed (DPFusion.compose f g).
Proof.
move=> /allowedP[a ha] /allowedP[b hb]; apply/allowedP; exists (a*b)=> x hx.
rewrite DPFusion.compose_in // hb ?DPFusion.map_into // ha //.
exact: esym (conjgM _ _ _).
Qed.

Lemma image_allowed (P Q : {group N}) (f : DPFusion.map P Q) :
  allowed f -> allowed (DPFusion.to_image f).
Proof.
move=> /allowedP[g hg]; apply/allowedP; exists g=> x hx.
by rewrite DPFusion.to_image_in // hg.
Qed.

Lemma inverse_allowed (P Q : {group N}) (f : DPFusion.map P Q) :
  allowed f -> allowed (DPFusion.inverse f).
Proof.
move=> /allowedP[g hg]; apply/allowedP; exists g^-1=> y hy.
have hx := DPFusion.map_into (DPFusion.inverse f) hy.
have ht := congr1 (fun z : G => z ^ g^-1) (hg _ hx).
rewrite DPFusion.inverse_cancel_right // conjgK in ht; exact: esym ht.
Qed.

Definition system : DPFusionSystem.system N :=
  @DPFusionSystem.FusionSystem N allowed conjugation_allowed composition_allowed image_allowed inverse_allowed.

Lemma system_allowed (P Q : {group N}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed system f = allowed f.
Proof. reflexivity. Qed.

End Construction.
End DPFiniteGroupFusionEmbedding.
