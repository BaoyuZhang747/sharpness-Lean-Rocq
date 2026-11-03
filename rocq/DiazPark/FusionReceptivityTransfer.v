From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionSaturationImage FusionConjugacy FusionReceptivity.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionReceptivityTransfer.

Section Transfer.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q : {group S}.
Variable theta : DPFusion.map P Q.
Hypothesis theta_allowed : DPFusionSystem.allowed F theta.
Hypothesis onto : DPFusion.image theta = Q.
Variable eta : DPFusion.map 'N(P)%G [set: S]%G.
Hypothesis eta_extends : {in P, eta =1 theta}.

Lemma normalizer_source_image : DPFusion.map_morphism eta @* P = Q.
Proof.
have heq : DPFusion.map_morphism eta @* P = DPFusion.map_morphism theta @* P.
  rewrite !morphimEsub ?normG //.
  apply: eq_in_imset=> x Px; exact: eta_extends Px.
change (DPFusion.map_morphism eta @* P = val Q).
rewrite heq; change (val (DPFusion.image theta) = val Q).
by rewrite onto.
Qed.

Lemma normalizer_centralizer_image :
  DPFusion.map_morphism eta @* 'C(P) \subset 'C(Q).
Proof. rewrite -normalizer_source_image; exact: morphim_cent. Qed.

Lemma centralizer_in_normalizer_image :
  DPFusionSystem.fully_centralized F P -> 'C(Q) \subset DPFusion.image eta.
Proof.
move=> hP.
have hPQ : DPFusionSystem.conjugate F P Q.
  apply/existsP; exists theta; by rewrite theta_allowed onto eqxx.
have hc : (#|'C(Q)| <= #|'C(P)|)%N := implyP (forallP hP Q) hPQ.
have heq : DPFusion.map_morphism eta @* 'C(P) = 'C(Q).
  apply/eqP; rewrite eqEcard normalizer_centralizer_image /=.
  by rewrite (card_injm (DPFusion.map_injm eta) (cent_sub P)).
rewrite -heq; exact: morphimS (cent_sub P).
Qed.

Hypothesis eta_allowed : DPFusionSystem.allowed F eta.
Hypothesis cent_image : 'C(Q) \subset DPFusion.image eta.

Section OneExtension.
Variable A : {group S}.
Variable psi : DPFusion.map A P.
Hypothesis psi_allowed : DPFusionSystem.allowed F psi.
Hypothesis psi_onto : DPFusion.image psi = P.

Let kappa := DPFusion.compose psi theta.

Lemma transfer_witness s t :
  s \in 'N(A) -> t \in 'N(P) ->
  {in A, forall x, psi (x ^ s) = (psi x) ^ t} ->
  {in A, forall x, kappa (x ^ s) = (kappa x) ^ (eta t)}.
Proof.
move=> Ns Nt hs x Ax.
have Axs : x ^ s \in A by rewrite memJ_norm.
have Px : psi x \in P := DPFusion.map_into psi Ax.
have Pxt : (psi x) ^ t \in P by rewrite memJ_norm.
rewrite /kappa !DPFusion.compose_in // hs //.
rewrite -(eta_extends Pxt) -(eta_extends Px).
exact: (morphJ (DPFusion.map_morphism eta) (subsetP (normG P) _ Px) Nt).
Qed.

Lemma transfer_domain :
  DPFusionSaturation.extension_domain psi \subset
    DPFusionSaturation.extension_domain kappa.
Proof.
apply/subsetP=> s /setIdP[Ns /exists_inP[t Nt /forall_inP ht]].
have hcompat : {in A, forall x, kappa (x ^ s) = (kappa x) ^ (eta t)}.
  apply: (@transfer_witness s t Ns Nt)=> x Ax; exact: (eqP (ht x Ax)).
apply/setIdP; split=> //; apply/exists_inP; exists (eta t).
- have h := DPFusionSaturationImage.compatible_normalizes_image Ns hcompat.
  by rewrite (DPFusionConjugacy.compose_onto psi_onto onto) in h.
- by apply/forall_inP=> x Ax; apply/eqP; exact: hcompat x Ax.
Qed.

Variable xi : DPFusion.map (DPFusionSaturation.extension_domain kappa) [set: S]%G.
Hypothesis xi_extends : {in A, xi =1 kappa}.

Lemma transfer_extension_image :
  DPFusion.image (DPFusion.restrict xi transfer_domain) \subset DPFusion.image eta.
Proof.
apply/subsetP=> y /morphimP[s Ns _ ->].
change (DPFusion.restrict xi transfer_domain s \in DPFusion.image eta).
rewrite DPFusion.restrict_in //.
have /setIdP[NsA /exists_inP[t Nt /forall_inP ht]] := Ns.
have hcompat : {in A, forall x, kappa (x ^ s) = (kappa x) ^ (eta t)}.
  apply: (@transfer_witness s t NsA Nt)=> x Ax; exact: (eqP (ht x Ax)).
have Nsk : s \in DPFusionSaturation.extension_domain kappa := subsetP transfer_domain s Ns.
have hconj : {in Q, forall q, q ^ (xi s) = q ^ (eta t)}.
  move=> q Qq.
  have Ik : DPFusion.image kappa = Q := DPFusionConjugacy.compose_onto psi_onto onto.
  rewrite -Ik in Qq; have /morphimP[x Ax _ hx] := Qq.
  change (q = kappa x) in hx; rewrite hx.
  have Axs : x ^ s \in A by rewrite memJ_norm.
  have Nx : x \in DPFusionSaturation.extension_domain kappa :=
    subsetP (DPFusionSaturation.source_extension_domain kappa) x Ax.
  have hm : xi (x ^ s) = (xi x) ^ (xi s) := morphJ (DPFusion.map_morphism xi) Nx Nsk.
  rewrite (xi_extends Axs) (xi_extends Ax) in hm.
  rewrite -hm.
  exact: hcompat x Ax.
have hcent : xi s * (eta t)^-1 \in 'C(Q).
  apply/centP=> q Qq; apply/commgP; rewrite commg1_sym.
  apply/conjg_fixP; by rewrite conjgM (hconj q Qq) conjgK.
have hratio := subsetP cent_image _ hcent.
have htI : eta t \in DPFusion.image eta := DPFusion.image_mem eta Nt.
have hprod := groupM hratio htI.
by rewrite mulgKV in hprod.
Qed.

End OneExtension.

Theorem transfer_receptive :
  DPFusionReceptivity.receptive F Q -> DPFusionReceptivity.receptive F P.
Proof.
move=> hrec A psi hpsi ontopsi.
pose kappa := DPFusion.compose psi theta.
have hk : DPFusionSystem.allowed F kappa := DPFusionSystem.composition_closed hpsi theta_allowed.
have onk : DPFusion.image kappa = Q := DPFusionConjugacy.compose_onto ontopsi onto.
have [xi [hxi hext]] := hrec A kappa hk onk.
pose domain_sub := @transfer_domain A psi ontopsi.
pose range_sub := @transfer_extension_image A psi ontopsi xi hext.
pose lifted := DPFusion.corestrict range_sub.
pose back := DPFusion.compose lifted (DPFusion.inverse eta).
pose final := DPFusion.compose back (DPFusion.inclusion (subsetT 'N(P))).
exists final; split.
- apply: DPFusionSystem.composition_closed; last exact: DPFusionSystem.inclusion_allowed.
  apply: DPFusionSystem.composition_closed; last exact: DPFusionSystem.inverse_closed eta_allowed.
  apply: DPFusionSystem.corestriction_allowed.
  exact: DPFusionSystem.restriction_allowed hxi.
- move=> x Ax.
  have Nx : x \in DPFusionSaturation.extension_domain psi :=
    subsetP (DPFusionSaturation.source_extension_domain psi) x Ax.
  have Px : psi x \in P := DPFusion.map_into psi Ax.
  rewrite /final /back !DPFusion.compose_in // DPFusion.inclusion_in ?DPFusion.map_into //.
  rewrite /lifted DPFusion.corestrict_in // DPFusion.restrict_in //.
  rewrite hext // /kappa DPFusion.compose_in // -(eta_extends Px).
  exact: DPFusion.inverse_cancel (subsetP (normG P) _ Px).
Qed.

End Transfer.
End DPFusionReceptivityTransfer.




