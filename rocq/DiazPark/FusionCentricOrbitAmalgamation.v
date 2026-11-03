From mathcomp Require Import all_ssreflect all_fingroup generic_quotient pgroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionSaturation
  FusionCentricBasics FusionCentricRestriction FusionCentricAmalgamation FusionCentricInclusionSpans.
Import DPFusionOrbit DPFusionCentricInclusionSpans.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricOrbitAmalgamation.
Section Amalgamation.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.
Variables U A B T : {group S}.
Hypotheses (sUA : U \subset A) (sUB : U \subset B).
Hypothesis cU : DPFusionSystem.centric F U.
Variables (gamma : orbit_hom F U T) (alpha : orbit_hom F A T) (beta : orbit_hom F B T).
Hypothesis agreeA : orbit_compose (DPFusionCentricRestriction.orbit_inclusion F sUA) alpha = gamma.
Hypothesis agreeB : orbit_compose (DPFusionCentricRestriction.orbit_inclusion F sUB) beta = gamma.
Local Notation D := ('N_A(U) <*> 'N_B(U))%G.

Lemma source_sub_domain : U \subset D.
Proof. apply: subset_trans (joing_subl _ _); by rewrite subsetI sUA normG. Qed.

Theorem orbit_normalizer_amalgamation :
  exists delta : orbit_hom F D T,
    orbit_compose (DPFusionCentricRestriction.orbit_inclusion F source_sub_domain) delta = gamma.
Proof.
have get_witness (V : {group S}) (sUV : U \subset V) (f : orbit_hom F V T) :
    orbit_compose (DPFusionCentricRestriction.orbit_inclusion F sUV) f = gamma ->
    exists q, q \in T /\ {in U, forall u,
      DPFusion.map_fun (val (repr gamma)) u = (DPFusion.map_fun (val (repr f)) u) ^ q}.
  move=> heq.
  rewrite -(reprK f) -(reprK gamma) /DPFusionCentricRestriction.orbit_inclusion orbit_compose_class in heq.
  move/orbit_class_eq/exists_inP: heq=> [q Tq /forall_inP hq].
  exists q; split=> // u Uu.
  have h := eqP (hq u Uu).
  rewrite /arrow_value /DPFusionSystem.arrow_compose /= DPFusion.compose_in // DPFusion.inclusion_in // in h.
have [qa [Tqa hqa]] := get_witness A sUA alpha agreeA.
have [qb [Tqb hqb]] := get_witness B sUB beta agreeB.
have [delta [hd hext]] := @DPFusionCentricAmalgamation.normalizer_amalgamation S F p sat
  U A B T sUA sUB (val (repr gamma)) (valP (repr gamma)) cU
  (val (repr alpha)) (val (repr beta)) qa qb Tqa Tqb hqa hqb.
pose rawdelta : DPFusionSystem.arrow F D T := Sub delta hd.
exists (orbit_class rawdelta).
rewrite /DPFusionCentricRestriction.orbit_inclusion orbit_compose_class -(reprK gamma).
apply: congr1; apply: DPFusionSystem.arrow_ext=> u Uu.
rewrite /DPFusionSystem.arrow_compose /= DPFusion.compose_in // DPFusion.inclusion_in //.
exact: hext u Uu.
Qed.

End Amalgamation.
End DPFusionCentricOrbitAmalgamation.
