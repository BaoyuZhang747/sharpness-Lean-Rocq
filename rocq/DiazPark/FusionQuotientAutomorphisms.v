From mathcomp Require Import all_ssreflect all_fingroup center pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionQuotientMaps FusionQuotientConstruction FusionQuotientNormalization
  GroupInfrastructure GroupQuotientInfrastructure.
Import DPFusion DPFusionQuotientConstruction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientAutomorphisms.

Section Endomorphism.
Variable S : finGroupType.
Variable P : {group S}.
Variable f : DPFusion.map P P.

Lemma endomorphism_onto : DPFusion.map_morphism f @* P = P.
Proof.
have h := morphim_fixP (DPFusion.map_injm f) P (subxx P).
apply/h.
exact: DPFusion.image_sub.
Qed.

Definition map_automorphism : {perm S} := aut (DPFusion.map_injm f) endomorphism_onto.

Lemma map_automorphismE x : x \in P -> map_automorphism x = f x.
Proof. exact: autE. Qed.

Lemma map_automorphism_in_Aut : map_automorphism \in Aut P.
Proof. exact: Aut_aut. Qed.

Lemma map_automorphism_allowed (F : DPFusionSystem.system S) :
  DPFusionSystem.allowed F f -> map_automorphism \in DPFusionSaturation.aut_group F P.
Proof.
move=> Ff; apply/setIdP; split; first exact: map_automorphism_in_Aut.
apply/existsP; exists f; apply/andP; split=> //.
by apply/forall_inP=> x Px; rewrite map_automorphismE.
Qed.

End Endomorphism.

Section QuotientAutomorphisms.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable P : {group coset_of Z}.
Let A := DPFusionSaturation.aut_group F (preimage P).
Let B := DPFusionSaturation.aut_group (system cZ) P.

Definition automorphism_relation (a : {perm S}) (b : {perm coset_of Z}) :=
  (b \in B) && [forall x in preimage P, b (coset Z x) == coset Z (a x)].

Lemma exists_quotient_automorphism a :
  a \in A -> exists b : {perm coset_of Z}, automorphism_relation a b.
Proof.
move=> /setIdP[aAut /existsP[f /andP[Ff /forall_inP hf]]].
have [b hb] := @exists_descended S F Z cZ P P f Ff.
have Fb : DPFusionSystem.allowed (system cZ) b.
  apply/existsP; exists f; by apply/andP.
exists (map_automorphism b); apply/andP; split.
- exact: map_automorphism_allowed Fb.
- apply/forall_inP=> x Px.
  have cPx : coset Z x \in P by rewrite -(preimage_mem cZ).
  by rewrite map_automorphismE // (@descendsE S Z P P f b hb x Px) (eqP (hf x Px)).
Qed.

Definition automorphism (a : {perm S}) : {perm coset_of Z} :=
  odflt 1 [pick b : {perm coset_of Z} | automorphism_relation a b].

Lemma automorphism_relation_holds a : a \in A -> automorphism_relation a (automorphism a).
Proof.
move=> aA; have [b hb] := exists_quotient_automorphism aA.
rewrite /automorphism; case: pickP=> [b' hb' | hnone] //.
by have := hnone b; rewrite hb.
Qed.

Lemma automorphism_allowed a : a \in A -> automorphism a \in B.
Proof. by move=> /automorphism_relation_holds /andP[]. Qed.

Lemma automorphismE a : a \in A -> forall x, x \in preimage P ->
  automorphism a (coset Z x) = coset Z (a x).
Proof.
move=> /automorphism_relation_holds /andP[_ /forall_inP h] x Px.
exact: eqP (h x Px).
Qed.

Lemma automorphism_in_Aut a : a \in A -> automorphism a \in Aut P.
Proof.
move=> aA; exact: subsetP (DPFusionSaturation.aut_group_sub (system cZ) P)
  (automorphism a) (automorphism_allowed aA).
Qed.

Lemma automorphism_morphic : {in A &, {morph automorphism : a b / a * b}}.
Proof.
move=> a b aA bA.
apply: (eq_Aut (automorphism_in_Aut (groupM aA bA))
  (groupM (automorphism_in_Aut aA) (automorphism_in_Aut bA))).
move=> q Pq.
have xP := repr_mem cZ Pq.
have aAut := subsetP (DPFusionSaturation.aut_group_sub F (preimage P)) a aA.
have axP := Aut_closed aAut xP.
rewrite -(coset_reprK q) (automorphismE (groupM aA bA) xP) !permM
  (automorphismE aA xP) (automorphismE bA axP).
by [].
Qed.

Canonical automorphism_morphism := Morphism automorphism_morphic.

Lemma automorphism_surjective : automorphism_morphism @* A = B.
Proof.
apply/setP=> b; apply/idP/idP.
- move=> /morphimP[a aA _ ->]; exact: automorphism_allowed.
- move=> bB.
  have /setIdP[bAut /existsP[g /andP[Fg /forall_inP hg]]] := bB.
  have /existsP[f /andP[Ff hf]] := Fg.
  have aA : map_automorphism f \in A := map_automorphism_allowed Ff.
  have eqb : automorphism (map_automorphism f) = b.
    apply: (eq_Aut (automorphism_in_Aut aA) bAut)=> q Pq.
    have xP := repr_mem cZ Pq.
    rewrite -(coset_reprK q) (automorphismE aA xP) map_automorphismE //.
    rewrite -(@descendsE S Z P P f g hf _ xP) coset_reprK.
    exact: eqP (hg q Pq).
  by apply/morphimP; exists (map_automorphism f).
Qed.

Lemma automorphism_fixes_kernel a : a \in A -> {in Z, a =1 id}.
Proof.
move=> /setIdP[aAut /existsP[f /andP[Ff /forall_inP hf]]].
have fixZ := DPFusionQuotient.central_fixes cZ (kernel_sub_preimage P) Ff.
move=> z Zz.
rewrite -(eqP (hf z (subsetP (kernel_sub_preimage P) z Zz))).
exact: fixZ.
Qed.

Lemma automorphism_kernel_pgroup (pi : nat_pred) :
  pi.-group Z -> pi.-group ('ker automorphism_morphism).
Proof.
move=> piZ.
exact (@quotient_automorphism_kernel_pgroup S (preimage P) Z A
  (normal_cosetpre P) (DPFusionSaturation.aut_group_sub F (preimage P))
  (fun a aA => @automorphism_fixes_kernel a aA) automorphism_morphism
  (fun a aA x xP => @automorphismE a aA x xP) pi piZ).
Qed.

Lemma coset_normalizes s :
  s \in 'N(preimage P) -> coset Z s \in 'N(P).
Proof.
move=> Ns.
have hs : s \in preimage 'N(P)%G.
  by rewrite (@DPFusionQuotientNormalization.normalizer_preimage S F Z cZ P).
by rewrite (preimage_mem cZ) in hs.
Qed.

Lemma repr_normalizes s :
  s \in 'N(P) -> repr s \in 'N(preimage P).
Proof.
move=> Ns.
have hs : repr s \in preimage 'N(P)%G.
  by rewrite (preimage_mem cZ) coset_reprK.
by rewrite (@DPFusionQuotientNormalization.normalizer_preimage S F Z cZ P) in hs.
Qed.

Lemma conjugation_in_ambient s : s \in 'N(preimage P) ->
  conj_aut (preimage P) s \in DPFusionSaturation.ambient_aut_group (preimage P).
Proof. by move=> Ns; apply/morphimP; exists s. Qed.

Lemma automorphism_conjugation s : s \in 'N(preimage P) ->
  automorphism (conj_aut (preimage P) s) = conj_aut P (coset Z s).
Proof.
move=> Ns.
have aA := subsetP (DPFusionSaturation.ambient_aut_sub F (preimage P))
  _ (conjugation_in_ambient Ns).
have bAut : conj_aut P (coset Z s) \in Aut P by exact: Aut_aut.
apply: (eq_Aut (automorphism_in_Aut aA) bAut)=> q Pq.
have xP := repr_mem cZ Pq.
have cPx : coset Z (repr q) \in P by rewrite coset_reprK.
rewrite -(coset_reprK q) (automorphismE aA xP)
  !norm_conj_autE // ?coset_normalizes //.
by rewrite morphJ ?(normZ_all cZ).
Qed.

Lemma ambient_automorphism_image :
  automorphism_morphism @* DPFusionSaturation.ambient_aut_group (preimage P) =
  DPFusionSaturation.ambient_aut_group P.
Proof.
apply/setP=> b; apply/idP/idP.
- move=> /morphimP[a _ /morphimP[s Ns _ ->] ->].
  change (automorphism (conj_aut (preimage P) s) \in
    DPFusionSaturation.ambient_aut_group P).
  rewrite automorphism_conjugation //.
  apply/morphimP; exists (coset Z s)=> //; exact: coset_normalizes Ns.
- move=> /morphimP[s Ns _ ->].
  have Nr := repr_normalizes Ns.
  have aU := conjugation_in_ambient Nr.
  have aA := subsetP (DPFusionSaturation.ambient_aut_sub F (preimage P)) _ aU.
  apply/morphimP; exists (conj_aut (preimage P) (repr s))=> //.
  change (conj_aut P s = automorphism (conj_aut (preimage P) (repr s))).
  by rewrite automorphism_conjugation // coset_reprK.
Qed.

Lemma fully_normalized_sylow (p : nat) :
  DPFusionSaturation.saturated F p ->
  DPFusionSystem.fully_normalized (system cZ) P ->
  p.-Sylow(B) (DPFusionSaturation.ambient_aut_group P).
Proof.
move=> sat hP.
have hpre : DPFusionSystem.fully_normalized F (preimage P).
  by rewrite -(@DPFusionQuotientNormalization.fully_normalized_preimage S F Z cZ P).
have [_ syl] := DPFusionSaturation.saturation_fully_normalized sat hpre.
have hs := morphim_pSylow automorphism_morphism
  (DPFusionSaturation.ambient_aut_sub F (preimage P)) syl.
by rewrite automorphism_surjective ambient_automorphism_image in hs.
Qed.

Lemma kernel_sub_ambient (p : nat) :
  p.-group Z -> DPFusionSaturation.saturated F p ->
  DPFusionSystem.fully_normalized (system cZ) P ->
  'ker automorphism_morphism \subset DPFusionSaturation.ambient_aut_group (preimage P).
Proof.
move=> pZ sat hP.
have hpre : DPFusionSystem.fully_normalized F (preimage P).
  by rewrite -(@DPFusionQuotientNormalization.fully_normalized_preimage S F Z cZ P).
have [_ syl] := DPFusionSaturation.saturation_fully_normalized sat hpre.
exact: normal_pgroup_sub_sylow (ker_normal automorphism_morphism)
  (automorphism_kernel_pgroup pZ) syl.
Qed.

End QuotientAutomorphisms.
End DPFusionQuotientAutomorphisms.
