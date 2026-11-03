From mathcomp Require Import all_ssreflect all_fingroup quotient generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionSaturation
  FusionAutomorphisms FusionOrbit FusionOuterAutomorphisms FusionOuterOrbit FusionOuterAction.
Import DPFusion DPFusionAutomorphisms DPFusionOrbit DPFusionOuter DPFusionOuterOrbit DPFusionOuterAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionOuterEndomorphisms.
Section Endomorphisms.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : {group S}.
Local Notation G := (outer_group F P).

Lemma aut_orbit_map_aut (f : DPFusionSystem.arrow F P P) :
  aut_orbit F P (map_aut (val f)) = orbit_class f.
Proof.
rewrite /aut_orbit; apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Px.
rewrite aut_mapE ?map_aut_allowed ?(valP f) //.
exact: map_autE Px.
Qed.

Definition outer_endomorphism (g : [subg G]) : orbit_hom F P P :=
  outer_orbit F (val g).

Definition endomorphism_outer (f : orbit_hom F P P) : [subg G] :=
  Subg (mem_quotient (inner P) (map_aut_allowed (valP (repr f)))).

Lemma outer_endomorphism_injective : injective outer_endomorphism.
Proof.
move=> g h e; apply: val_inj.
have [Ag eg] := representative_spec (valP g).
have [Ah eh] := representative_spec (valP h).
have eqc := proj1 (aut_orbit_coset_eq Ag Ah) e.
by rewrite eg eh in eqc.
Qed.

Lemma endomorphism_outerK : cancel endomorphism_outer outer_endomorphism.
Proof.
move=> f; rewrite /outer_endomorphism /endomorphism_outer /=.
rewrite outer_orbit_coset ?map_aut_allowed ?(valP (repr f)) //.
rewrite aut_orbit_map_aut; exact: reprK.
Qed.

Lemma outer_endomorphismK : cancel outer_endomorphism endomorphism_outer.
Proof.
move=> g; apply: outer_endomorphism_injective.
exact: endomorphism_outerK.
Qed.

Theorem outer_endomorphism_bijective : bijective outer_endomorphism.
Proof. exists endomorphism_outer; [exact: outer_endomorphismK | exact: endomorphism_outerK]. Qed.

Lemma outer_endomorphism_one : outer_endomorphism 1 = orbit_identity F P.
Proof. exact: outer_orbit_one. Qed.

Lemma outer_endomorphism_mul (g h : [subg G]) :
  outer_endomorphism (g*h) = orbit_compose (outer_endomorphism g) (outer_endomorphism h).
Proof. exact: (outer_orbit_mul (valP g) (valP h)). Qed.

End Endomorphisms.
End DPFusionOuterEndomorphisms.


