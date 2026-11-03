From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow generic_quotient.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionOrbit
  FusionAutomorphisms FusionOuterAutomorphisms FusionOuterOrbit FusionOuterAction.
Import DPFusion DPFusionOrbit DPFusionAutomorphisms DPFusionOuter DPFusionOuterOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionOuterCard.
Section Cardinality.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : {group S}.
Local Notation G := (outer_group F P).
Local Notation outer_orbit := (@DPFusionOuterAction.outer_orbit S F P).

Lemma outer_orbit_injective : {in G &, injective outer_orbit}.
Proof.
move=> g h Gg Gh e.
have [Ag eg] := DPFusionOuterAction.representative_spec Gg.
have [Ah eh] := DPFusionOuterAction.representative_spec Gh.
rewrite -eg -eh.
exact: (proj1 (aut_orbit_coset_eq Ag Ah) e).
Qed.

Lemma outer_orbit_surjective (f : orbit_hom F P P) :
  exists g, g \in G /\ outer_orbit g = f.
Proof.
move: f; apply: quotW=> f.
pose a := map_aut (val f).
have Aa : a \in DPFusionSaturation.aut_group F P := map_aut_allowed (valP f).
exists (coset (inner P) a); split; first exact: mem_quotient _ Aa.
rewrite DPFusionOuterAction.outer_orbit_coset // /aut_orbit.
apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Px.
by rewrite aut_mapE // map_autE.
Qed.

Theorem endomorphism_card_outer : #|[set: orbit_hom F P P]| = #|G|.
Proof.
have E : [set: orbit_hom F P P] = outer_orbit @: G.
  apply/setP=> f; rewrite inE; symmetry; apply/imsetP.
  have [g [Gg <-]] := outer_orbit_surjective f; by exists g.
rewrite E card_in_imset //; exact: outer_orbit_injective.
Qed.

End Cardinality.
Section Top.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis sat : DPFusionSaturation.saturated F p.

Lemma top_fully_normalized : DPFusionSystem.fully_normalized F [set: S]%G.
Proof. apply/forallP=> Q; apply/implyP=> _; by rewrite normT cardsT max_card. Qed.

Lemma top_ambient_outer_trivial : ambient_outer_group [set: S]%G = 1%G.
Proof.
apply: val_inj.
change (DPFusionSaturation.ambient_aut_group [set: S]%G / inner [set: S]%G = 1).
change ((conj_aut [set: S]%G @* 'N([set: S])) / inner [set: S]%G = 1).
have eI := congr1 (fun A : {set S} => conj_aut [set: S]%G @* A) (@normT S).
rewrite eI -/(inner _); exact: trivg_quotient.
Qed.

Lemma top_outer_coprime : coprime p #|outer_group F [set: S]%G|.
Proof.
have h := ambient_outer_sylow sat top_fully_normalized.
rewrite top_ambient_outer_trivial /pHall indexg1 in h.
have /and3P[_ _ hn] := h.
by rewrite prime_coprime // -p'natE.
Qed.

Theorem top_endomorphism_coprime : coprime p #|[set: orbit_hom F [set: S]%G [set: S]%G]|.
Proof. rewrite endomorphism_card_outer; exact: top_outer_coprime. Qed.

End Top.
End DPFusionOuterCard.



