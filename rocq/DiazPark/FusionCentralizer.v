From mathcomp Require Import all_ssreflect all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionCentralizerMaps.
Import DPFusion DPFusionSubgroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentralizer.
Section Construction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Local Notation C := 'C(E)%G.
Local Notation T := [subg C]%type.

Definition joint (P : {group T}) : {group S} := (ambient P <*> E)%G.

Lemma joint_left (P : {group T}) : ambient P \subset joint P.
Proof. exact: joing_subl. Qed.

Lemma joint_right (P : {group T}) : E \subset joint P.
Proof. exact: joing_subr. Qed.

Definition allowed (P Q : {group T}) (f : DPFusion.map P Q) :=
  [exists fhat : DPFusion.map (joint P) (joint Q),
    [&& DPFusionSystem.allowed F fhat,
      [forall x in P, fhat (val x) == val (f x)] &
      [forall e in E, fhat e == e]]].

Lemma allowedP (P Q : {group T}) (f : DPFusion.map P Q) :
  reflect (exists fhat : DPFusion.map (joint P) (joint Q),
    DPFusionSystem.allowed F fhat /\
    (forall x : T, x \in P -> fhat (val x) = val (f x)) /\ {in E, fhat =1 id})
    (allowed f).
Proof.
apply: (iffP existsP).
- move=> [fhat /and3P[hf /forall_inP hext /forall_inP hfix]].
  exists fhat; split=> //; split.
  + by move=> x Px; apply/eqP; exact: hext x Px.
  + by move=> e Ee; apply/eqP; exact: hfix e Ee.
- move=> [fhat [hf [hext hfix]]]; exists fhat; apply/and3P; split=> //.
  + by apply/forall_inP=> x Px; apply/eqP; exact: hext x Px.
  + by apply/forall_inP=> e Ee; apply/eqP; exact: hfix e Ee.
Qed.

Lemma conjugation_joint (P Q : {group T}) (s : T) (sPQ : P :^ s \subset Q) :
  joint P :^ (val s) \subset joint Q.
Proof.
rewrite /joint conjYg join_subG; apply/andP; split.
- apply/subsetP=> _ /imsetP[x /morphimP[y _ Py ->] ->].
  change (val (y ^ s) \in joint Q).
  apply: (subsetP (joing_subl (ambient Q) E)); apply: ambient_mem.
  apply: (subsetP sPQ); by rewrite memJ_conjg.
- have Ns : val s \in 'N(E) := subsetP (cent_sub E) _ (valP s).
  by rewrite (normP Ns); exact: joing_subr.
Qed.

Lemma conjugation_allowed (P Q : {group T}) (s : T) (sPQ : P :^ s \subset Q) :
  allowed (DPFusion.conjugation sPQ).
Proof.
apply/allowedP; exists (DPFusion.conjugation (conjugation_joint sPQ)); split.
- exact: DPFusionSystem.conjugation_closed.
- split.
  + move=> x Px; rewrite !DPFusion.conjugation_in //.
    exact: subsetP (joint_left P) _ (ambient_mem Px).
  + move=> e Ee; rewrite DPFusion.conjugation_in ?(subsetP (joint_right P) e Ee) //.
    by rewrite conjgE -(centP (valP s) e Ee) mulKg.
Qed.

Lemma composition_allowed (P Q R : {group T})
    (f : DPFusion.map P Q) (g : DPFusion.map Q R) :
  allowed f -> allowed g -> allowed (DPFusion.compose f g).
Proof.
move/allowedP=> [fhat [hf [hext hfix]]]; move/allowedP=> [ghat [hg [gext gfix]]].
apply/allowedP; exists (DPFusion.compose fhat ghat); split.
- exact: DPFusionSystem.composition_closed hf hg.
- split.
  + move=> x Px; rewrite DPFusion.compose_in ?(subsetP (joint_left P) _ (ambient_mem Px)) //.
    by rewrite hext // gext ?DPFusion.map_into // DPFusion.compose_in.
  + move=> e Ee; rewrite DPFusion.compose_in ?(subsetP (joint_right P) e Ee) //.
    by rewrite hfix // gfix.
Qed.

Lemma extension_image_left (P Q : {group T}) (f : DPFusion.map P Q)
    (fhat : DPFusion.map (joint P) (joint Q))
    (hext : forall x : T, x \in P -> fhat (val x) = val (f x)) :
  DPFusion.map_morphism fhat @* ambient P = ambient (DPFusion.image f).
Proof.
apply/setP=> z; apply/idP/idP.
- case/morphimP=> x _ /morphimP[y _ Py ->] ->.
  change (fhat (val y) \in ambient (DPFusion.image f)).
  rewrite hext //; apply: ambient_mem; exact: DPFusion.image_mem Py.
- case/morphimP=> x _ /morphimP[y Py _ ->] ->.
  apply/morphimP; exists (val y).
  + exact: subsetP (joint_left P) _ (ambient_mem Py).
  + exact: ambient_mem Py.
  + exact: esym (hext y Py).
Qed.

Lemma extension_image_right (P Q : {group T})
    (fhat : DPFusion.map (joint P) (joint Q)) (hfix : {in E, fhat =1 id}) :
  DPFusion.map_morphism fhat @* E = E.
Proof.
apply/setP=> z; apply/idP/idP.
- by case/morphimP=> x _ Ex ->; rewrite DPFusion.map_morphismE hfix.
- move=> Ez; apply/morphimP; exists z=> //.
  + exact: subsetP (joint_right P) z Ez.
  + exact: esym (hfix z Ez).
Qed.

Lemma extension_image (P Q : {group T}) (f : DPFusion.map P Q)
    (fhat : DPFusion.map (joint P) (joint Q))
    (hext : forall x : T, x \in P -> fhat (val x) = val (f x))
    (hfix : {in E, fhat =1 id}) : DPFusion.image fhat = joint (DPFusion.image f).
Proof.
apply: val_inj; change (DPFusion.map_morphism fhat @* (ambient P <*> E) =
  ambient (DPFusion.image f) <*> E).
by rewrite morphimY ?joint_left ?joint_right //
  (extension_image_left hext) (extension_image_right hfix).
Qed.

Lemma image_allowed (P Q : {group T}) (f : DPFusion.map P Q) :
  allowed f -> allowed (DPFusion.to_image f).
Proof.
move/allowedP=> [fhat [hf [hext hfix]]].
have sI : DPFusion.image fhat \subset joint (DPFusion.image f).
  by rewrite (extension_image hext hfix).
apply/allowedP; exists (DPFusion.corestrict sI); split.
- exact: DPFusionSystem.corestriction_allowed hf.
- split.
  + move=> x Px; rewrite DPFusion.corestrict_in ?(subsetP (joint_left P) _ (ambient_mem Px)) //.
    by rewrite hext // DPFusion.to_image_in.
  + move=> e Ee; rewrite DPFusion.corestrict_in ?(subsetP (joint_right P) e Ee) //.
    exact: hfix.
Qed.

Lemma inverse_allowed (P Q : {group T}) (f : DPFusion.map P Q) :
  allowed f -> allowed (DPFusion.inverse f).
Proof.
move/allowedP=> [fhat [hf [hext hfix]]].
have sI : joint (DPFusion.image f) \subset DPFusion.image fhat.
  by rewrite (extension_image hext hfix).
apply/allowedP; exists (DPFusion.restrict (DPFusion.inverse fhat) sI); split.
- exact: DPFusionSystem.restriction_allowed (DPFusionSystem.inverse_closed hf).
- split.
  + move=> x Ix; have /morphimP[y Py _ ey] := Ix.
    change (x = f y) in ey; subst x.
    have Ify : f y \in DPFusion.image f := DPFusion.image_mem f Py.
    rewrite DPFusion.restrict_in ?(subsetP (joint_left (DPFusion.image f)) _ (ambient_mem Ify)) //.
    rewrite -(hext y Py) DPFusion.inverse_cancel ?(subsetP (joint_left P) _ (ambient_mem Py)) //.
    by rewrite DPFusion.inverse_cancel.
  + move=> e Ee; rewrite DPFusion.restrict_in ?(subsetP (joint_right (DPFusion.image f)) e Ee) //.
    have eJ : e \in joint P := subsetP (joint_right P) e Ee.
    have := DPFusion.inverse_cancel fhat eJ.
    by rewrite hfix.
Qed.

Definition system : DPFusionSystem.system [the finGroupType of T] :=
  @DPFusionSystem.FusionSystem [the finGroupType of T] allowed
    conjugation_allowed composition_allowed image_allowed inverse_allowed.

Lemma hom_iff (P Q : {group T}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed system f <->
  exists fhat : DPFusion.map (joint P) (joint Q),
    DPFusionSystem.allowed F fhat /\
    (forall x : T, x \in P -> fhat (val x) = val (f x)) /\ {in E, fhat =1 id}.
Proof. by split; [move/allowedP | move=> h; apply/allowedP]. Qed.

End Construction.
End DPFusionCentralizer.
