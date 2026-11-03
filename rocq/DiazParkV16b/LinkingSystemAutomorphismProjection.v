(** The actual surjective automorphism-group homomorphism
    Aut_L(P) -> Aut_F(P), derived from the standard linking projection. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionSaturation FusionAutomorphisms.
From DiazParkV16b Require Import LinkingSystem LinkingSystemFinite LinkingSystemAutomorphisms.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingFinite DPLinkingAutomorphisms DPFusionAutomorphisms.
Local Open Scope group_scope.

Module DPLinkingAutomorphismProjection.
Section MapAutomorphisms.
Variable S : finGroupType.

Lemma map_aut_identity (P : {group S}) : map_aut (DPFusion.identity P) = 1.
Proof.
apply: (eq_Aut (map_aut_mem _) (group1 (Aut P)))=> x Px.
by rewrite map_autE // DPFusion.identity_in // perm1.
Qed.

Lemma map_aut_compose (P : {group S}) (f g : DPFusion.map P P) :
    map_aut (DPFusion.compose f g) = map_aut f * map_aut g.
Proof.
apply: (eq_Aut (map_aut_mem _) (groupM (map_aut_mem f) (map_aut_mem g)))=> x Px.
rewrite (map_autE (DPFusion.compose f g) Px) (DPFusion.compose_in f g Px) permM
  (map_autE f Px) (map_autE g (DPFusion.map_into f Px)).
reflexivity.
Qed.

Lemma map_aut_injective (P : {group S}) : injective (@map_aut S P).
Proof.
move=> f g he; apply DPFusion.map_ext=> x Px.
by rewrite -(map_autE f Px) he map_autE.
Qed.
End MapAutomorphisms.

Section Projection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable P : DPFusionOrbit.centric_object F.
Local Notation G := (automorphism_group L P).
Local Notation AF := (DPFusionSaturation.aut_group F (val P)).
Local Notation H := [subg AF]%type.

Definition projection_value (a : G) : H :=
  Sub (map_aut (val (linking_projection L a))) (map_aut_allowed (valP (linking_projection L a))).

Lemma projection_value_perm (a : G) :
    val (projection_value a) = map_aut (val (linking_projection L a)).
Proof. reflexivity. Qed.

Lemma projection_value_mul (a b : G) : projection_value (a * b) = projection_value a * projection_value b.
Proof.
apply val_inj; change (map_aut (val (linking_projection L (linking_compose L a b))) =
  map_aut (val (linking_projection L a)) * map_aut (val (linking_projection L b))).
rewrite projection_compose; exact: map_aut_compose.
Qed.

Definition projection : {morphism [set: G] >-> H}.
Proof.
apply: (Morphism (mfun := projection_value)); move=> a b _ _; exact: projection_value_mul.
Defined.

Lemma projection_perm (a : G) :
    val (projection a) = map_aut (val (linking_projection L a)).
Proof. reflexivity. Qed.

Lemma projection_apply (a : G) (x : S) : x \in val P ->
    val (projection a) x = DPFusion.map_fun (val (linking_projection L a)) x.
Proof. exact: map_autE. Qed.

Theorem projection_surjective : forall b : H, exists a : G, projection a = b.
Proof.
move=> b.
have bAut : val b \in Aut (val P) := subsetP (DPFusionSaturation.aut_group_sub F (val P)) _ (valP b).
pose raw : DPFusionSystem.arrow F (val P) (val P) :=
  Sub (aut_to_map bAut) (aut_to_map_allowed bAut (valP b)).
exists (chosen_lift L raw); apply val_inj.
rewrite projection_perm chosen_lift_projection; exact: map_aut_to_map.
Qed.

Lemma projection_image : projection @* [set: G] = [set: H].
Proof.
apply/setP=> b; rewrite inE; apply/morphimP.
have [a ha] := projection_surjective b.
exists a; [by rewrite inE | by rewrite inE | exact: esym ha].
Qed.

Lemma projection_eq_one_iff (a : G) :
    projection a = 1 <-> linking_projection L a = DPFusionSystem.arrow_identity F (val P).
Proof.
split=> ha.
- apply val_inj; apply map_aut_injective.
  rewrite map_aut_identity.
  exact (congr1 (fun b : H => val b) ha).
- apply val_inj; rewrite projection_perm ha; exact: map_aut_identity.
Qed.
End Projection.
End DPLinkingAutomorphismProjection.

Check DPLinkingAutomorphismProjection.projection.
Check DPLinkingAutomorphismProjection.projection_surjective.
Check DPLinkingAutomorphismProjection.projection_eq_one_iff.
Print Assumptions DPLinkingAutomorphismProjection.projection_surjective.
Print Assumptions DPLinkingAutomorphismProjection.projection_eq_one_iff.
