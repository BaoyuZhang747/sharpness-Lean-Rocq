From mathcomp Require Import all_ssreflect all_fingroup center pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionAutomorphisms FusionQuotientMaps FusionQuotientConstruction
  FusionQuotientNormalization FusionQuotientAutomorphisms.
Import DPFusion DPFusionQuotientConstruction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientExtension.
Section Extension.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable p : nat.
Hypothesis pZ : p.-group Z.
Hypothesis sat : DPFusionSaturation.saturated F p.
Variables P Q : {group coset_of Z}.
Variable b : DPFusion.map P Q.
Variable f : DPFusion.map (preimage P) (preimage Q).
Hypothesis Ff : DPFusionSystem.allowed F f.
Hypothesis hf : descends f b.
Hypothesis onto : DPFusion.image b = Q.
Hypothesis hQ : DPFusionSystem.fully_normalized (system cZ) Q.

Lemma lift_image : DPFusion.image f = preimage Q.
Proof. exact: (@lift_onto S F Z cZ P Q f b Ff hf onto). Qed.

Lemma extension_domain_lift :
  preimage (DPFusionSaturation.extension_domain b) \subset
    DPFusionSaturation.extension_domain f.
Proof.
apply/subsetP=> s hs.
have /setIdP[Nsb /exists_inP[t Nt /forall_inP ht]] :
    coset Z s \in DPFusionSaturation.extension_domain b.
  by rewrite -(preimage_mem cZ).
have Ns : s \in 'N(preimage P).
  have h : s \in preimage 'N(P)%G by rewrite (preimage_mem cZ).
  by rewrite (@DPFusionQuotientNormalization.normalizer_preimage S F Z cZ P) in h.
pose a := conj_aut (preimage P) s.
have aA : a \in DPFusionSaturation.aut_group F (preimage P).
  apply: (subsetP (DPFusionSaturation.ambient_aut_sub F (preimage P))).
  by apply/morphimP; exists s.
have aAut := subsetP (DPFusionSaturation.aut_group_sub F (preimage P)) a aA.
pose d := DPFusionAutomorphisms.aut_transport f a.
have dA : d \in DPFusionSaturation.aut_group F (preimage Q).
  have h := DPFusionAutomorphisms.aut_transport_allowed Ff aA.
  by rewrite lift_image in h.
have dbar : DPFusionQuotientAutomorphisms.automorphism cZ Q d = conj_aut Q t.
  have dAut := DPFusionQuotientAutomorphisms.automorphism_in_Aut cZ dA.
  have tAut : conj_aut Q t \in Aut Q by exact: Aut_aut.
  apply: (eq_Aut dAut tAut)=> q Qq.
  have xQ : repr q \in preimage Q := repr_mem cZ Qq.
  rewrite -lift_image in xQ.
  have /morphimP[x Px _ hx] := xQ.
  have cPx : coset Z x \in P by rewrite -(preimage_mem cZ).
  have Pxs : x ^ s \in preimage P by rewrite memJ_norm.
  have hc := eqP (ht (coset Z x) cPx).
  have cosetJ : (coset Z x) ^ (coset Z s) = coset Z (x ^ s).
    by rewrite morphJ ?(normZ_all cZ).
  rewrite cosetJ (@descendsE S Z P Q f b hf _ Pxs)
    (@descendsE S Z P Q f b hf _ Px) in hc.
  rewrite -(coset_reprK q) hx.
  change (DPFusionQuotientAutomorphisms.automorphism cZ Q d (coset Z (f x)) =
    conj_aut Q t (coset Z (f x))).
  have Ifx : f x \in preimage Q := DPFusion.map_into f Px.
  rewrite (DPFusionQuotientAutomorphisms.automorphismE cZ dA Ifx).
  rewrite /d (DPFusionAutomorphisms.aut_transportE f aAut Px).
  rewrite /a !norm_conj_autE //.
  by rewrite -(preimage_mem cZ).
have dU : d \in DPFusionSaturation.ambient_aut_group (preimage Q).
  have hker := @DPFusionQuotientAutomorphisms.kernel_sub_ambient S F Z cZ Q p pZ sat hQ.
  have hU := DPFusionSaturation.ambient_aut_sub F (preimage Q).
  rewrite -(morphimGK hker hU).
  apply/morphpreP; split=> //.
  rewrite DPFusionQuotientAutomorphisms.ambient_automorphism_image.
  change (DPFusionQuotientAutomorphisms.automorphism cZ Q d \in
    DPFusionSaturation.ambient_aut_group Q).
  rewrite dbar; by apply/morphimP; exists t.
have /morphimP[u Nu _ eu] := dU.
apply/setIdP; split=> //; apply/exists_inP; exists u=> //.
apply/forall_inP=> x Px; apply/eqP.
have h := DPFusionAutomorphisms.aut_transportE f aAut Px.
rewrite /a norm_conj_autE // in h.
rewrite -h; change (d (f x) = (f x) ^ u).
rewrite eu norm_conj_autE //.
exact: DPFusion.map_into Px.
Qed.

Lemma extension_domain_descend :
  DPFusionSaturation.extension_domain f \subset
    preimage (DPFusionSaturation.extension_domain b).
Proof.
apply/subsetP=> s /setIdP[Ns /exists_inP[t Nt /forall_inP ht]].
rewrite (preimage_mem cZ); apply/setIdP; split.
- exact: (@DPFusionQuotientAutomorphisms.coset_normalizes S F Z cZ P s Ns).
- apply/exists_inP; exists (coset Z t).
  + exact: (@DPFusionQuotientAutomorphisms.coset_normalizes S F Z cZ Q t Nt).
  + apply/forall_inP=> q Pq; apply/eqP.
    have xP := repr_mem cZ Pq.
    have xsP : repr q ^ s \in preimage P by rewrite memJ_norm.
    have hc := congr1 (coset Z) (eqP (ht _ xP)).
    have hJ : coset Z (repr q) ^ coset Z s = coset Z (repr q ^ s).
      by rewrite morphJ ?(normZ_all cZ).
    rewrite -(coset_reprK q) hJ (@descendsE S Z P Q f b hf _ xsP)
      (@descendsE S Z P Q f b hf _ xP).
    rewrite hc; by rewrite morphJ ?(normZ_all cZ).
Qed.

Lemma extension_domain_preimage :
  preimage (DPFusionSaturation.extension_domain b) = DPFusionSaturation.extension_domain f.
Proof.
apply: val_inj; apply/eqP; rewrite eqEsubset; apply/andP; split.
- exact: extension_domain_lift.
- exact: extension_domain_descend.
Qed.

Lemma quotient_extension :
  exists bhat : DPFusion.map (DPFusionSaturation.extension_domain b) [set: coset_of Z]%G,
    DPFusionSystem.allowed (system cZ) bhat /\ {in P, bhat =1 b}.
Proof.
have hpre : DPFusionSystem.fully_normalized F (preimage Q).
  by rewrite -(@DPFusionQuotientNormalization.fully_normalized_preimage S F Z cZ Q).
have [hFC _] := DPFusionSaturation.saturation_fully_normalized sat hpre.
have [fhat [Fhat hext]] := DPFusionSaturation.saturation_extension sat Ff lift_image hFC.
pose g0 := DPFusion.restrict fhat extension_domain_lift.
have sI : DPFusion.image g0 \subset preimage [set: coset_of Z]%G.
  by apply/subsetP=> x _; rewrite (preimage_mem cZ) inE.
pose g := DPFusion.corestrict sI.
have Fg : DPFusionSystem.allowed F g.
  apply: DPFusionSystem.corestriction_allowed.
  exact: DPFusionSystem.restriction_allowed extension_domain_lift Fhat.
have [bhat hbhat] := @exists_descended S F Z cZ
  (DPFusionSaturation.extension_domain b) [set: coset_of Z]%G g Fg.
exists bhat; split.
- apply/existsP; exists g; by apply/andP.
- move=> q Pq.
  have xP := repr_mem cZ Pq.
  have xN : repr q \in preimage (DPFusionSaturation.extension_domain b).
    rewrite (preimage_mem cZ) coset_reprK.
    exact: subsetP (DPFusionSaturation.source_extension_domain b) q Pq.
  rewrite -(coset_reprK q)
    (@descendsE S Z (DPFusionSaturation.extension_domain b) [set: coset_of Z]%G g bhat hbhat _ xN).
  rewrite /g DPFusion.corestrict_in // /g0 DPFusion.restrict_in // (hext _ xP).
  exact: esym (@descendsE S Z P Q f b hf _ xP).
Qed.

End Extension.
End DPFusionQuotientExtension.
