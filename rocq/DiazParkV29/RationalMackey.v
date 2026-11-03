(** Remark 3.3: the genuine rational degree-zero Mackey functor. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp rat.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure
  MackeyStructures MackeyFusionMinimal FusionSystems FusionOrbit FusionMackeyShape.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyOrbitCoefficient
  GroupCohomologyMackeyNative GroupCohomologyMackeyPushBase GroupCohomologyMackeyInclusions
  GroupCohomologyMackeyPushIso.
From DiazParkV29 Require Import RationalDegreeZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPFusionMackey DPV29RationalDegreeZero
  DPGroupCohomologyMackeyNative DPGroupCohomologyMackeyPushBase
  DPGroupCohomologyMackeyInclusions.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPV29RationalMackey.
Section Mackey.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Local Notation Qrat := [the comPzRingType of (rat : Type)].
Local Notation A := [the lmodType Qrat of Qrat^o].
Definition rational_mackey := @native_cohomology_mackey S F Qrat A 0.

Lemma pull_coordinate (P Q : {group S}) (a : DPFusionSystem.arrow F P Q)
    (x : mackey_value rational_mackey Q) :
  coordinate (mackey_pull rational_mackey (orbit_class a) x) = coordinate x.
Proof. rewrite native_mackey_pull; exact: coordinate_pull. Qed.

Lemma transfer_coordinate (P Q : {group S}) (h : P \subset Q)
    (x : mackey_value rational_mackey P) :
  coordinate (mackey_push rational_mackey (orbit_class (inclusion_arrow F h)) x) =
    coordinate x *+ indexg Q P.
Proof. rewrite native_mackey_push raw_push_inclusion; exact: coordinate_transfer. Qed.

Lemma conjugation_coordinate (P Q : {group S})
    (a : DPFusionSystem.arrow F P Q) (b : DPFusionSystem.arrow F Q P)
    (hab : DPFusionSystem.arrow_compose a b = DPFusionSystem.arrow_identity F P)
    (x : mackey_value rational_mackey P) :
  coordinate (mackey_push rational_mackey (orbit_class a) x) = coordinate x.
Proof.
rewrite native_mackey_push (DPGroupCohomologyMackeyPushIso.raw_push_inverse A 0 hab).
exact: coordinate_pull.
Qed.

Lemma coordinate_injective (P : {group S}) :
  injective (@coordinate Qrat A [the finGroupType of [subg P]%type]).
Proof. exact: can_inj (@constant_coordinate Qrat A [the finGroupType of [subg P]%type]). Qed.

Lemma coordinate_zero (P : {group S}) :
  @coordinate Qrat A [the finGroupType of [subg P]%type] 0 = 0.
Proof. exact (module_hom_zero (@coordinate_hom Qrat A [the finGroupType of [subg P]%type])). Qed.

Lemma rational_value_nonzero (P : {group S}) :
    exists x : mackey_value rational_mackey P, x <> 0.
Proof.
exists (@constant_class Qrat A [the finGroupType of [subg P]%type] 1) => h.
have e := congr1 (@coordinate Qrat A [the finGroupType of [subg P]%type]) h.
rewrite coordinate_constant coordinate_zero in e.
have eb : (1 : rat) == 0 by apply/eqP; exact e.
exact (negP (oner_neq0 rat) eb).
Qed.

Theorem rational_mackey_simple : mackey_simple rational_mackey.
Proof.
split; first by exists (1%G : {group S}); exact: rational_value_nonzero.
move=> N.
case: (pselect (forall P x, subfunctor_value N P x -> x = 0)) => [hz|hz]; first by left.
right.
have [P [x [hx hne]]] : exists P, exists x : mackey_value rational_mackey P,
    subfunctor_value N P x /\ x <> 0.
  case: (pselect (exists P, exists x : mackey_value rational_mackey P,
    subfunctor_value N P x /\ x <> 0)) => [he|hn]; first exact he.
  exfalso; apply hz => P x hx.
  case: (pselect (x = 0)) => [e|he]; first exact e.
  exfalso; apply hn; exists P, x; exact (conj hx he).
pose a := inclusion_arrow F (sub1G P).
pose y := mackey_pull rational_mackey (orbit_class a) x.
have hy : subfunctor_value N 1%G y := @subfunctor_pull Qrat (orbit_category F) (fusion_mackey_shape F) rational_mackey N 1%G P (orbit_class a) x hx.
have ey : coordinate y != 0.
  apply/eqP => e; apply hne; apply (@coordinate_injective P).
  rewrite /y pull_coordinate in e.
  by rewrite coordinate_zero e.
move=> U v.
pose b := inclusion_arrow F (sub1G U).
pose z := mackey_push rational_mackey (orbit_class b) y.
have hzmem : subfunctor_value N U z := @subfunctor_push Qrat (orbit_category F) (fusion_mackey_shape F) rational_mackey N 1%G U (orbit_class b) y hy.
have ez : coordinate z != 0.
  rewrite /z transfer_coordinate -mulr_natl mulf_neq0 //.
  by rewrite Num.Theory.pnatr_eq0 -lt0n indexg_gt0.
have hv := @subspace_scale Qrat _ (subfunctor_value N U)
  (coordinate v / coordinate z) z hzmem.
have ev : (coordinate v / coordinate z) *: z = v.
  apply (@coordinate_injective U).
  change (module_hom_fun (@coordinate_hom Qrat A [the finGroupType of [subg U]%type])
    ((coordinate v / coordinate z) *: z) = coordinate v).
  rewrite module_hom_scale.
  change (coordinate v / coordinate z * coordinate z = coordinate v).
  by rewrite mulfVK.
by rewrite ev in hv.
Qed.

Theorem rational_minimal_iff (P : {group S}) :
  DPMackeyMinimal.subgroup_minimal rational_mackey P <-> P = 1%G.
Proof.
split.
- move=> [hn hsmall]; apply/eqP.
  apply/negP => hp.
  have hlt : (1%G : {group S}) \proper P by rewrite proper1G; apply/negP; exact hp.
  have [x hx] := rational_value_nonzero 1%G.
  exact (hx (hsmall _ hlt x)).
- move=> ->; split; first exact: rational_value_nonzero.
  move=> L hL x.
  have hf : ~~ ((1%G : {group S}) \subset L) := proper_subn hL.
  by move: hf; rewrite sub1G.
Qed.

Theorem rational_centralizer_counterexample (nontrivial : [set: S] != 1%G) :
  mackey_simple rational_mackey /\
  (exists x : mackey_value rational_mackey [set: S], x <> 0) /\
  ~ exists L : {group S}, DPMackeyMinimal.subgroup_minimal rational_mackey L /\
    'C(L) \subset L.
Proof.
split; first exact: rational_mackey_simple.
split; first exact: rational_value_nonzero.
move=> [L [hL hc]].
have e := proj1 (rational_minimal_iff L) hL.
rewrite e cent1T subTset in hc.
apply (negP nontrivial); by rewrite eq_sym.
Qed.

End Mackey.
End DPV29RationalMackey.
