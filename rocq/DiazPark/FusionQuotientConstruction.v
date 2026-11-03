From mathcomp Require Import all_ssreflect all_fingroup center.
From DiazPark Require Import FusionMaps FusionSystems FusionQuotientMaps.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientConstruction.

Section Construction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.

Definition preimage (P : {group coset_of Z}) : {group S} :=
  (coset Z @*^-1 P)%G.

Lemma normZ_all x : x \in 'N(Z).
Proof.
by apply: (subsetP (normal_norm (DPFusionQuotient.central_normal cZ))); rewrite inE.
Qed.

Lemma preimage_mem (P : {group coset_of Z}) x :
  (x \in preimage P) = (coset Z x \in P).
Proof.
apply/idP/idP.
- by move=> /morphpreP[_ h].
- move=> h; apply/morphpreP; split=> //; exact: normZ_all.
Qed.

Lemma repr_mem (P : {group coset_of Z}) q :
  q \in P -> repr q \in preimage P.
Proof. by rewrite preimage_mem coset_reprK. Qed.

Lemma kernel_sub_preimage P : Z \subset preimage P.
Proof. exact: sub_cosetpre. Qed.

Lemma preimage_quotient P : (preimage P / Z)%G = P.
Proof. apply: val_inj; exact: cosetpreK. Qed.

Definition descends (P Q : {group coset_of Z})
    (f : DPFusion.map (preimage P) (preimage Q)) (b : DPFusion.map P Q) :=
  [forall x in preimage P, b (coset Z x) == coset Z (f x)].

Definition allowed (P Q : {group coset_of Z}) (b : DPFusion.map P Q) :=
  [exists f : DPFusion.map (preimage P) (preimage Q),
    DPFusionSystem.allowed F f && descends f b].

Lemma descendsE (P Q : {group coset_of Z})
    (f : DPFusion.map (preimage P) (preimage Q)) (b : DPFusion.map P Q) :
  descends f b -> forall x, x \in preimage P ->
    b (coset Z x) = coset Z (f x).
Proof. by move=> /forall_inP hf x Px; exact: eqP (hf x Px). Qed.

Lemma exists_descended (P Q : {group coset_of Z})
    (f : DPFusion.map (preimage P) (preimage Q)) :
  DPFusionSystem.allowed F f -> exists b : DPFusion.map P Q, descends f b.
Proof.
move=> Ff.
have fixZ := DPFusionQuotient.central_fixes cZ (kernel_sub_preimage P) Ff.
pose b := DPFusionQuotient.quotient_map (DPFusionQuotient.central_normal cZ)
  (kernel_sub_preimage P) fixZ.
have hex : exists b : DPFusion.map (preimage P / Z)%G (preimage Q / Z)%G,
    forall x, x \in preimage P -> b (coset Z x) = coset Z (f x).
  exists b; move=> x Px; exact: DPFusionQuotient.quotient_mapE.
rewrite !preimage_quotient in hex.
case: hex=> q hq; exists q; apply/forall_inP=> x Px; apply/eqP; exact: hq x Px.
Qed.

Lemma descends_image_quotient (P Q : {group coset_of Z})
    (f : DPFusion.map (preimage P) (preimage Q)) (b : DPFusion.map P Q) :
  descends f b -> DPFusion.image f / Z = DPFusion.image b.
Proof.
move=> hf; apply/setP=> y; apply/idP/idP.
- move=> /morphimP[x _ /morphimP[z Pz _ ->] ->].
  change (coset Z (f z) \in DPFusion.image b).
  rewrite -(descendsE hf Pz); apply: DPFusion.image_mem.
  by rewrite -preimage_mem.
- move=> /morphimP[q Pq _ ->].
  change (b q \in DPFusion.image f / Z).
  have Pr := repr_mem Pq.
  rewrite -(coset_reprK q) (descendsE hf Pr).
  apply: mem_quotient; exact: DPFusion.image_mem Pr.
Qed.

Lemma descends_image_preimage (P Q : {group coset_of Z})
    (f : DPFusion.map (preimage P) (preimage Q)) (b : DPFusion.map P Q) :
  DPFusionSystem.allowed F f -> descends f b ->
  DPFusion.image f = preimage (DPFusion.image b).
Proof.
move=> Ff hf.
have fixZ := DPFusionQuotient.central_fixes cZ (kernel_sub_preimage P) Ff.
have sZI : Z \subset DPFusion.image f.
  apply/subsetP=> z Zz; rewrite -(fixZ z Zz).
  apply: DPFusion.image_mem; exact: subsetP (kernel_sub_preimage P) z Zz.
have nZI : Z <| DPFusion.image f := normalS sZI (subsetT _) (DPFusionQuotient.central_normal cZ).
apply: val_inj.
by rewrite /preimage /= -(descends_image_quotient hf) quotientGK.
Qed.

Lemma conjugation_allowed (P Q : {group coset_of Z}) (q : coset_of Z)
    (sPQ : P :^ q \subset Q) : allowed (DPFusion.conjugation sPQ).
Proof.
have prePQ : preimage P :^ repr q \subset preimage Q.
  apply/subsetP=> y /imsetP[x Px ->]; rewrite preimage_mem.
  rewrite morphJ ?normZ_all //.
  change ((coset Z x) ^ (coset Z (repr q)) \in Q).
  rewrite coset_reprK.
  apply: (subsetP sPQ); apply/imsetP; exists (coset Z x)=> //.
  by rewrite -preimage_mem.
apply/existsP; exists (DPFusion.conjugation prePQ); apply/andP; split.
- exact: DPFusionSystem.conjugation_closed.
- apply/forall_inP=> x Px; apply/eqP.
  have cPx : coset Z x \in P by rewrite -preimage_mem.
  rewrite !DPFusion.conjugation_in // morphJ ?normZ_all //.
  change ((coset Z x) ^ q = (coset Z x) ^ (coset Z (repr q))).
  by rewrite coset_reprK.
Qed.

Lemma composition_allowed (P Q R : {group coset_of Z})
    (b : DPFusion.map P Q) (d : DPFusion.map Q R) :
  allowed b -> allowed d -> allowed (DPFusion.compose b d).
Proof.
move=> /existsP[f /andP[Ff hf]] /existsP[g /andP[Fg hg]].
apply/existsP; exists (DPFusion.compose f g); apply/andP; split.
- exact: DPFusionSystem.composition_closed Ff Fg.
- apply/forall_inP=> x Px; apply/eqP.
  have cPx : coset Z x \in P by rewrite -preimage_mem.
  have Qfx := DPFusion.map_into f Px.
  by rewrite !DPFusion.compose_in // (descendsE hf Px) (descendsE hg Qfx).
Qed.

Lemma image_allowed (P Q : {group coset_of Z}) (b : DPFusion.map P Q) :
  allowed b -> allowed (DPFusion.to_image b).
Proof.
move=> /existsP[f /andP[Ff hf]].
have sI : DPFusion.image f \subset preimage (DPFusion.image b).
  by rewrite (descends_image_preimage Ff hf).
apply/existsP; exists (DPFusion.corestrict sI); apply/andP; split.
- exact: DPFusionSystem.corestriction_allowed sI Ff.
- apply/forall_inP=> x Px; apply/eqP.
  have cPx : coset Z x \in P by rewrite -preimage_mem.
  by rewrite DPFusion.to_image_in // DPFusion.corestrict_in // (descendsE hf Px).
Qed.

Lemma inverse_allowed (P Q : {group coset_of Z}) (b : DPFusion.map P Q) :
  allowed b -> allowed (DPFusion.inverse b).
Proof.
move=> /existsP[f /andP[Ff hf]].
have sI : preimage (DPFusion.image b) \subset DPFusion.image f.
  by rewrite (descends_image_preimage Ff hf).
pose g := DPFusion.restrict (DPFusion.inverse f) sI.
apply/existsP; exists g; apply/andP; split.
- exact: DPFusionSystem.restriction_allowed sI (DPFusionSystem.inverse_closed Ff).
- apply/forall_inP=> x Px; apply/eqP.
  have cIx : coset Z x \in DPFusion.image b by rewrite -preimage_mem.
  have Pgx := DPFusion.map_into g Px.
  have cPgx : coset Z (g x) \in P by rewrite -preimage_mem.
  apply: (DPFusion.map_injective (f := b) (DPFusion.map_into (DPFusion.inverse b) cIx) cPgx).
  rewrite DPFusion.inverse_cancel_right // (descendsE hf Pgx).
  rewrite /g DPFusion.restrict_in // DPFusion.inverse_cancel_right //.
  exact: subsetP sI x Px.
Qed.

Definition system : DPFusionSystem.system (coset_of Z) :=
  @DPFusionSystem.FusionSystem (coset_of Z) allowed
    conjugation_allowed composition_allowed image_allowed inverse_allowed.

Lemma allowed_iff_lift (P Q : {group coset_of Z}) (b : DPFusion.map P Q) :
  DPFusionSystem.allowed system b <->
  exists f : DPFusion.map (preimage P) (preimage Q),
    DPFusionSystem.allowed F f /\
    forall x, x \in preimage P -> b (coset Z x) = coset Z (f x).
Proof.
split.
- move=> /existsP[f /andP[Ff hf]]; exists f; split=> //.
  exact: descendsE hf.
- move=> [f [Ff hf]]; apply/existsP; exists f; apply/andP; split=> //.
  by apply/forall_inP=> x Px; apply/eqP; exact: hf x Px.
Qed.

Lemma lift_onto (P Q : {group coset_of Z})
    (f : DPFusion.map (preimage P) (preimage Q)) (b : DPFusion.map P Q) :
  DPFusionSystem.allowed F f -> descends f b -> DPFusion.image b = Q ->
  DPFusion.image f = preimage Q.
Proof. by move=> Ff hf imQ; rewrite (descends_image_preimage Ff hf) imQ. Qed.

End Construction.
End DPFusionQuotientConstruction.
