From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems.
Import DPFusion.

(** The two ordinary saturation axioms, on actual automorphism groups and
    the actual extension-domain subgroup.  No extension/generation theorem
    is incorporated as an additional field. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionSaturation.

Section ExtensionDomain.
Variable S : finGroupType.

Definition extension_set (P Q : {group S}) (f : DPFusion.map P Q) :=
  [set s in 'N(P) |
    [exists t in 'N(Q), [forall x in P, f (x ^ s) == (f x) ^ t]]].

Lemma extension_group_set (P Q : {group S}) (f : DPFusion.map P Q) :
  group_set (extension_set f).
Proof.
apply/group_setP; split.
- apply/setIdP; split; first exact: group1.
  apply/exists_inP; exists (1 : S); first exact: group1.
  by apply/forall_inP=> x Px; rewrite !conjg1.
- move=> s1 s2 /setIdP[Ns1 /exists_inP[t1 Nt1 /forall_inP h1]]
    /setIdP[Ns2 /exists_inP[t2 Nt2 /forall_inP h2]].
  apply/setIdP; split; first exact: groupM Ns1 Ns2.
  apply/exists_inP; exists (t1 * t2); first exact: groupM Nt1 Nt2.
  apply/forall_inP=> x Px; apply/eqP.
  have Px1 : x ^ s1 \in P by rewrite memJ_norm.
  by rewrite !conjgM (eqP (h2 _ Px1)) (eqP (h1 _ Px)).
Qed.

Definition extension_domain (P Q : {group S}) (f : DPFusion.map P Q) : {group S} :=
  group (extension_group_set f).

Lemma extension_domain_normalizer (P Q : {group S}) (f : DPFusion.map P Q) :
  extension_domain f \subset 'N(P).
Proof. by apply/subsetP=> s /setIdP[Ns _]. Qed.

Lemma source_extension_domain (P Q : {group S}) (f : DPFusion.map P Q) :
  P \subset extension_domain f.
Proof.
apply/subsetP=> s Ps; apply/setIdP; split.
- exact: (subsetP (normG P) s Ps).
- apply/exists_inP; exists (f s).
  + apply: (subsetP (normG Q)); exact: DPFusion.map_into Ps.
  + apply/forall_inP=> x Px; apply/eqP.
    exact: (morphJ (DPFusion.map_morphism f) Px Ps).
Qed.

Lemma centralizer_extension_domain (P Q : {group S}) (f : DPFusion.map P Q) :
  'C(P) \subset extension_domain f.
Proof.
apply/subsetP=> s Cs; apply/setIdP; split.
- exact: (subsetP (cent_sub P) s Cs).
- apply/exists_inP; exists (1 : S); first exact: group1.
  apply/forall_inP=> x Px.
  have ex : x ^ s = x by rewrite conjgE -(centP Cs x Px) mulKg.
  by rewrite ex conjg1.
Qed.

End ExtensionDomain.

Section AutomorphismGroups.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition aut_set (P : {group S}) :=
  [set a in Aut P |
    [exists f : DPFusion.map P P,
      DPFusionSystem.allowed F f && [forall x in P, f x == a x]]].

Lemma aut_group_set (P : {group S}) : group_set (aut_set P).
Proof.
apply/group_setP; split.
- apply/setIdP; split; first exact: group1.
  apply/existsP; exists (DPFusion.identity P); apply/andP; split.
  + exact: DPFusionSystem.identity_allowed.
  + by apply/forall_inP=> x Px; rewrite DPFusion.identity_in // perm1.
- move=> a b /setIdP[Aa /existsP[f /andP[Ff /forall_inP hf]]]
    /setIdP[Ab /existsP[g /andP[Fg /forall_inP hg]]].
  apply/setIdP; split; first exact: groupM Aa Ab.
  apply/existsP; exists (DPFusion.compose f g); apply/andP; split.
  + exact: DPFusionSystem.composition_closed Ff Fg.
  + apply/forall_inP=> x Px; rewrite DPFusion.compose_in // permM.
    have Pfx : DPFusion.map_fun f x \in P := DPFusion.map_into f Px.
    by rewrite (eqP (hg _ Pfx)) (eqP (hf _ Px)).
Qed.

Definition aut_group (P : {group S}) : {group {perm S}} := group (aut_group_set P).

Lemma aut_group_sub (P : {group S}) : aut_group P \subset Aut P.
Proof. by apply/subsetP=> a /setIdP[Aa _]. Qed.

Definition ambient_aut_group (P : {group S}) : {group {perm S}} :=
  (conj_aut P @* 'N(P))%G.

Lemma ambient_aut_sub (P : {group S}) : ambient_aut_group P \subset aut_group P.
Proof.
apply/subsetP=> a /morphimP[s Ns _ ->]; apply/setIdP; split.
- exact: Aut_aut.
- have sPP : P :^ s \subset P by rewrite (normP Ns).
  apply/existsP; exists (DPFusion.conjugation sPP); apply/andP; split.
  + exact: DPFusionSystem.conjugation_closed.
  + apply/forall_inP=> x Px.
    by rewrite DPFusion.conjugation_in // norm_conj_autE.
Qed.

(** The usual Sylow and extension clauses, stated for an isomorphism onto Q.
    The image factorization in FusionSystems converts this to the manuscript's
    formulation for a morphism P -> S with fully centralized image. *)
Record saturated (p : nat) : Prop := Saturated {
  saturation_fully_normalized : forall P : {group S},
    DPFusionSystem.fully_normalized F P ->
    DPFusionSystem.fully_centralized F P /\
      p.-Sylow(aut_group P) (ambient_aut_group P);
  saturation_extension : forall (P Q : {group S}) (f : DPFusion.map P Q),
    DPFusionSystem.allowed F f -> DPFusion.image f = Q ->
    DPFusionSystem.fully_centralized F Q ->
    exists fhat : DPFusion.map (extension_domain f) [set: S]%G,
      DPFusionSystem.allowed F fhat /\ {in P, fhat =1 f}
}.

End AutomorphismGroups.

End DPFusionSaturation.
