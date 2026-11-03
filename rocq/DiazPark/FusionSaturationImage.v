From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionSaturationImage.

Section Domains.
Variable S : finGroupType.

Lemma image_corestrict (P Q R : {group S}) (f : DPFusion.map P Q)
    (sIR : DPFusion.image f \subset R) :
  DPFusion.image (DPFusion.corestrict sIR) = DPFusion.image f.
Proof.
apply: val_inj; change (DPFusion.map_morphism (DPFusion.corestrict sIR) @* P =
  DPFusion.map_morphism f @* P).
apply: eq_morphim=> x Px; exact: DPFusion.corestrict_in Px.
Qed.

Lemma image_to_image (P Q : {group S}) (f : DPFusion.map P Q) :
  DPFusion.image (DPFusion.to_image f) = DPFusion.image f.
Proof. exact: image_corestrict. Qed.

Definition intrinsic_extension_domain (P Q : {group S}) (f : DPFusion.map P Q) :=
  DPFusionSaturation.extension_domain (DPFusion.to_image f).

(** A compatible ambient conjugation automatically normalizes the actual image. *)
Lemma compatible_normalizes_image (P Q : {group S}) (f : DPFusion.map P Q)
    (s t : S) :
  s \in 'N(P) -> {in P, forall x, f (x ^ s) = (f x) ^ t} ->
  t \in 'N(DPFusion.image f).
Proof.
move=> Ns hf; rewrite inE; apply/subsetP=> y /imsetP[z Iz ->].
have /morphimP[x Px _ ->] := Iz.
rewrite -(hf x Px); apply: DPFusion.image_mem.
by rewrite memJ_norm.
Qed.

(** This is the manuscript's normalizer witness formula, with t ranging over S. *)
Lemma intrinsic_extension_domainE (P Q : {group S}) (f : DPFusion.map P Q) s :
  (s \in intrinsic_extension_domain f) =
  ((s \in 'N(P)) && [exists t : S, [forall x in P, f (x ^ s) == (f x) ^ t]]).
Proof.
apply/idP/idP.
- move=> /setIdP[Ns /exists_inP[t Nt /forall_inP ht]].
  apply/andP; split=> //; apply/existsP; exists t.
  apply/forall_inP=> x Px.
  have Pxs : x ^ s \in P by rewrite memJ_norm.
  have h := ht x Px.
  by rewrite !DPFusion.to_image_in in h.
- move=> /andP[Ns /existsP[t /forall_inP ht]].
  apply/setIdP; split=> //; apply/exists_inP; exists t.
  + apply: (@compatible_normalizes_image P Q f s t Ns)=> x Px.
    exact: (eqP (ht x Px)).
  + apply/forall_inP=> x Px.
    have Pxs : x ^ s \in P by rewrite memJ_norm.
    by rewrite !DPFusion.to_image_in //; exact: ht x Px.
Qed.

Lemma intrinsic_extension_domain_onto (P Q : {group S}) (f : DPFusion.map P Q) :
  DPFusion.image f = Q ->
  intrinsic_extension_domain f = DPFusionSaturation.extension_domain f.
Proof.
move=> imf; apply: val_inj; apply/setP=> s.
rewrite intrinsic_extension_domainE; apply/idP/idP.
- move=> /andP[Ns /existsP[t /forall_inP ht]].
  apply/setIdP; split=> //; apply/exists_inP; exists t.
  + rewrite -imf; apply: (@compatible_normalizes_image P Q f s t Ns)=> x Px.
    exact: (eqP (ht x Px)).
  + by apply/forall_inP=> x Px; exact: ht x Px.
- move=> /setIdP[Ns /exists_inP[t Nt ht]].
  by apply/andP; split=> //; apply/existsP; exists t.
Qed.

Lemma intrinsic_extension_domain_corestrict (P Q R : {group S})
    (f : DPFusion.map P Q) (sIR : DPFusion.image f \subset R) :
  intrinsic_extension_domain (DPFusion.corestrict sIR) = intrinsic_extension_domain f.
Proof.
apply: val_inj; apply/setP=> s; rewrite !intrinsic_extension_domainE.
case Ns: (s \in 'N(P))=> //=.
apply/idP/idP.
- move=> /existsP[t /forall_inP ht]; apply/existsP; exists t.
  apply/forall_inP=> x Px.
  have Pxs : x ^ s \in P by rewrite memJ_norm.
  have h := ht x Px; by rewrite !DPFusion.corestrict_in in h.
- move=> /existsP[t /forall_inP ht]; apply/existsP; exists t.
  apply/forall_inP=> x Px.
  have Pxs : x ^ s \in P by rewrite memJ_norm.
  by rewrite !DPFusion.corestrict_in //; exact: ht x Px.
Qed.

End Domains.

Section Saturation.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.

Lemma saturated_image_extension (sat : DPFusionSaturation.saturated F p)
    (P Q : {group S}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed F f ->
  DPFusionSystem.fully_centralized F (DPFusion.image f) ->
  exists fhat : DPFusion.map (intrinsic_extension_domain f) [set: S]%G,
    DPFusionSystem.allowed F fhat /\ {in P, fhat =1 f}.
Proof.
move=> hf hI.
have hi := DPFusionSystem.image_closed hf.
have [fhat [hhat hext]] := DPFusionSaturation.saturation_extension sat hi
  (image_to_image f) hI.
exists fhat; split=> //; move=> x Px.
by rewrite (hext x Px) DPFusion.to_image_in.
Qed.

Lemma saturated_of_image_extension
    (hSylow : forall P : {group S},
      DPFusionSystem.fully_normalized F P ->
      DPFusionSystem.fully_centralized F P /\
        p.-Sylow(DPFusionSaturation.aut_group F P)
          (DPFusionSaturation.ambient_aut_group P))
    (hExtension : forall (P Q : {group S}) (f : DPFusion.map P Q),
      DPFusionSystem.allowed F f ->
      DPFusionSystem.fully_centralized F (DPFusion.image f) ->
      exists fhat : DPFusion.map (intrinsic_extension_domain f) [set: S]%G,
        DPFusionSystem.allowed F fhat /\ {in P, fhat =1 f}) :
  DPFusionSaturation.saturated F p.
Proof.
constructor=> // P Q f hf imf hQ.
have hI : DPFusionSystem.fully_centralized F (DPFusion.image f) by rewrite imf.
have heq := intrinsic_extension_domain_onto imf.
have hex := hExtension P Q f hf hI.
by rewrite heq in hex.
Qed.

(** Exact equivalence with the manuscript: extension is tested only on P -> S. *)
Lemma saturated_iff_manuscript :
  DPFusionSaturation.saturated F p <->
  ((forall P : {group S}, DPFusionSystem.fully_normalized F P ->
      DPFusionSystem.fully_centralized F P /\
        p.-Sylow(DPFusionSaturation.aut_group F P)
          (DPFusionSaturation.ambient_aut_group P)) /\
   (forall (P : {group S}) (f : DPFusion.map P [set: S]%G),
      DPFusionSystem.allowed F f ->
      DPFusionSystem.fully_centralized F (DPFusion.image f) ->
      exists fhat : DPFusion.map (intrinsic_extension_domain f) [set: S]%G,
        DPFusionSystem.allowed F fhat /\ {in P, fhat =1 f})).
Proof.
split=> [sat | [hSylow hExtension]].
- split; first exact: DPFusionSaturation.saturation_fully_normalized sat.
  move=> P f hf hI; exact: (@saturated_image_extension sat P [set: S]%G f hf hI).
- apply: (@saturated_of_image_extension hSylow)=> P Q f hf hI.
  pose sIT := subset_trans (DPFusion.image_sub f) (subsetT Q).
  pose g := DPFusion.corestrict sIT.
  have hg : DPFusionSystem.allowed F g := DPFusionSystem.corestriction_allowed sIT hf.
  have hIg : DPFusionSystem.fully_centralized F (DPFusion.image g).
    by rewrite /g image_corestrict.
  have hex := hExtension P g hg hIg.
  have heq : intrinsic_extension_domain g = intrinsic_extension_domain f :=
    intrinsic_extension_domain_corestrict sIT.
  rewrite heq in hex; case: hex=> fhat [hhat hext].
  exists fhat; split=> // x Px.
  by rewrite (hext x Px) /g DPFusion.corestrict_in.
Qed.

End Saturation.
End DPFusionSaturationImage.
