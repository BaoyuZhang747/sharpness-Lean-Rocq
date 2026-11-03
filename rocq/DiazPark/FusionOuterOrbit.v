From mathcomp Require Import all_ssreflect all_fingroup quotient generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionSaturation
  FusionAutomorphisms FusionOrbit FusionOuterAutomorphisms.
Import DPFusion DPFusionAutomorphisms DPFusionOrbit DPFusionOuter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionOuterOrbit.
Section Orbit.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : {group S}.
Local Notation A := (DPFusionSaturation.aut_group F P).

Definition aut_map (a : {perm S}) : DPFusion.map P P :=
  aut_to_map (subsetP (DPFusionSaturation.aut_group_sub F P) _ (valP (subg A a))).

Lemma aut_map_allowed a : DPFusionSystem.allowed F (aut_map a).
Proof. apply: aut_to_map_allowed; exact: valP. Qed.

Lemma aut_mapE a : a \in A -> {in P, aut_map a =1 a}.
Proof. by move=> Aa x Px; rewrite /aut_map aut_to_mapE // subgK. Qed.

Definition aut_arrow a : DPFusionSystem.arrow F P P := Sub (aut_map a) (aut_map_allowed a).
Definition aut_orbit a : orbit_hom F P P := orbit_class (aut_arrow a).

Lemma aut_orbit_one : aut_orbit 1 = orbit_identity F P.
Proof.
rewrite /aut_orbit /orbit_identity.
apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Px.
rewrite DPFusion.identity_in // aut_mapE ?group1 // perm1.
by [].
Qed.

Lemma aut_orbit_mul a b : a \in A -> b \in A ->
  aut_orbit (a*b) = orbit_compose (aut_orbit a) (aut_orbit b).
Proof.
move=> Aa Ab; rewrite /aut_orbit orbit_compose_class.
apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Px.
change (aut_map (a*b) x = DPFusion.compose (aut_map a) (aut_map b) x).
rewrite DPFusion.compose_in //.
rewrite (aut_mapE (groupM Aa Ab) Px) (aut_mapE Ab (DPFusion.map_into (aut_map a) Px)) (aut_mapE Aa Px).
rewrite permM.
by [].
Qed.

Lemma aut_orbit_inner a : a \in inner P -> aut_orbit a = orbit_identity F P.
Proof.
move=> Ia; have Aa := subsetP (inner_sub F P) a Ia.
have /morphimP[r _ Pr er] := Ia.
symmetry; apply/orbit_class_eq/exists_inP; exists r=> //.
apply/forall_inP=> x Px; apply/eqP.
change (aut_map a x = (DPFusion.identity P x) ^ r).
by rewrite aut_mapE // DPFusion.identity_in // er conj_autE.
Qed.

Lemma aut_orbit_coset_eq a b : a \in A -> b \in A ->
  (aut_orbit a = aut_orbit b <-> coset (inner P) a = coset (inner P) b).
Proof.
move=> Aa Ab.
have Na := subsetP (normal_norm (inner_normal F P)) a Aa.
have Nb := subsetP (normal_norm (inner_normal F P)) b Ab.
split.
- move/orbit_class_eq/exists_inP=> [r Pr /forall_inP hr].
  have er : b = a * conj_aut P r.
    apply: (eq_Aut (subsetP (DPFusionSaturation.aut_group_sub F P) b Ab)
      (groupM (subsetP (DPFusionSaturation.aut_group_sub F P) a Aa) (Aut_aut _ _)))=> x Px.
    have axP := Aut_closed (subsetP (DPFusionSaturation.aut_group_sub F P) a Aa) Px.
    have h := eqP (hr x Px).
    change (aut_map b x = (aut_map a x) ^ r) in h.
    rewrite !aut_mapE // in h; by rewrite permM conj_autE.
  rewrite er coset_kerr //.
  exact: mem_morphim (subsetP (normG P) r Pr) Pr.
- move=> eqc; have [c Ic ec] := kercoset_rcoset Nb Na (esym eqc).
  have Ac := subsetP (inner_sub F P) c Ic.
  rewrite ec (aut_orbit_mul Ac Aa) (aut_orbit_inner Ic).
  exact: (esym (@Category.compose_id_left (orbit_category F) P P (aut_orbit a))).
Qed.

End Orbit.
End DPFusionOuterOrbit.




